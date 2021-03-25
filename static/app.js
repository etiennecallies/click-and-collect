// **************
// DISPLAY CONFIG
// **************

const UNARY_CONNECTORS = {
    'negation': '<span>¬</span>',
    'ofcourse': '<span>!</span>',
    'whynot': '<span>?</span>'
};

const BINARY_CONNECTORS = {
    'implication': '<span class="binary-connector">→</span>',
    'conjunction': '<span class="binary-connector">∧</span>',
    'disjunction': '<span class="binary-connector">∨</span>',
    'tensor': '<span class="binary-connector">⊗</span>',
    'par': '<span class="binary-connector flip">&</span>',
    'with': '<span class="binary-connector">&</span>',
    'plus': '<span class="binary-connector">⊕</span>',
    'lollipop': '<span class="binary-connector">⊸</span>'
};

const NEUTRAL_ELEMENTS = {
    'true': '<span>true</span>',
    'false': '<span>false</span>',
    'one': '<span>1</span>',
    'bottom': '<span>⊥</span>',
    'top': '<span>⊤</span>',
    'zero': '<span>0</span>'
};

const RULES = {
    'axiom': '<span class="italic">ax</span>',
    'tensor': '<span>⊗</span>',
    'par': '<span class="flip">&</span>',
    'with': '<span>&</span>',
    'plus_left': '<span>⊕<sub>1</sub></span>',
    'plus_right': '<span>⊕<sub>2</sub></span>',
    'one': '<span>1</span>',
    'bottom': '<span>⊥</span>',
    'top': '<span>⊤</span>',
    // rule zero does not exist
    'promotion': '<span>!</span>',
    'dereliction': '<span>?<span class="italic">d</span></span>',
    'contraction': '<span>?<span class="italic">c</span></span>',
    'weakening': '<span>?<span class="italic">w</span></span>'
};

// ***************************
// CLICK / DOUBLE CLICK CONFIG
// ***************************

const CLICK_DELAY = 200;
window.clickCount = 0;
window.clickTimer = null;

// *****************
// ON DOCUMENT READY
// *****************

$( function() {
    // SEQUENT FORM
    let $sequentForm = $('#sequent-form');
    $sequentForm.on('submit', function(e) {
        e.preventDefault(); // avoid to execute the actual submit of the form.
    });

    // PARSE URL
    let searchParams = new URLSearchParams(window.location.search);
    if (searchParams.has('s')) {
        $sequentForm.find($('input[name=sequentAsString]')).val(searchParams.get('s'));
        submitSequent($sequentForm);
    }
} );

// ************
// SEQUENT FORM
// ************

function submitSequent(element) {
    cleanSequentInput();

    let form = $(element).closest('form');
    let sequentAsString = form.find($('input[name=sequentAsString]')).val();

    // We update current URL by adding sequent in query parameters
    let currentUrl = new URL(window.location.href);
    currentUrl.searchParams.set('s', sequentAsString.toString());
    window.history.pushState("object or string", "Title", currentUrl.toString());

    let apiUrl = '/parse_sequent';

    $.ajax({
        type: 'GET',
        url: apiUrl,
        data: { sequentAsString },
        success: function(data)
        {
            if (data['is_valid']) {
                initProof(data['sequent_as_json']);
            } else {
                displayPedagogicError(data['error_message']);
            }
        },
        error: function(jqXHR, textStatus, errorThrown) {
            console.log(jqXHR);
            console.log(jqXHR.responseText);
            console.log(textStatus);
            console.log(errorThrown);
            alert('Technical error, check browser console for more details.');
        }
     });
}

function cleanSequentInput() {
    $('#main-proof-container').html('');
}

// ***************
// PEDAGOGIC ERROR
// ***************

function displayPedagogicError(errorMessage) {
    let $mainContainer = $('#main-proof-container');
    let $div = $mainContainer
        .children('div.pedagogic-error');
    if (!$div.length) {
        $div = $('<div>', {'class': 'pedagogic-error'});
        $div.append($('<div>', {'class': 'message'}));
        let $close = $('<div>', {'class': 'close-button'});
        $close.html('✖');
        $close.on('click', function () {cleanPedagogicError();});
        $div.append($close);
        $mainContainer.append($div);
    }
    $div.children('div.message').text(errorMessage);
}

function cleanPedagogicError() {
    $('#main-proof-container')
        .children('div.pedagogic-error')
        .remove();
}

// *************
// PROOF DISPLAY
// *************

function initProof(sequentAsJson) {
    console.log(sequentAsJson);
    let proofdiv = $('#main-proof-container');

    let $div = $('<div>', {'class': 'proofIsIncomplete'});
    let $div2 = $('<div>', {'class': 'proof'});
    $div2.append(createSequentTable(sequentAsJson));
    $div.append($div2);
    proofdiv.append($div);
}

function createSequentTable(sequentAsJson) {
    let $table = $('<table>');

    let $td = $('<td>');
    $td.append(createSequent(sequentAsJson));
    $table.append($td);

    let $tagBox = $('<td>', {'class': 'tagBox'})
        .html('&nbsp;');
    $table.append($tagBox);

    return $table;
}

function createSequent(sequentAsJson) {
    let $sequentDiv = $('<div>', {'class': 'sequent'})
        .data('sequent', sequentAsJson);

    if ('hyp' in sequentAsJson) {
        createFormulas(sequentAsJson, 'hyp', $sequentDiv);
    }

    let $thesisSpan = $('<span class="turnstile explained">⊢</span>');
    $thesisSpan.on('click', function () {
        applyRule('axiom', $sequentDiv, 0);
    });
    $sequentDiv.append($thesisSpan);

    if ('cons' in sequentAsJson) {
        createFormulas(sequentAsJson, 'cons', $sequentDiv);
    }

    return $sequentDiv;
}

function createFormulas(sequentAsJson, field, $sequentDiv) {
    let $ul = $('<ul>', {'class': ['commaList ' + field]})
        .sortable({
            helper : 'clone'
        });
    for (let i = 0; i < sequentAsJson[field].length; i++) {
        let formulaAsJson = sequentAsJson[field][i];
        let $li = $('<li>').data('initialPosition', i);

        // Build formula
        let $span = $('<span>', {'class': 'main-formula'})
            .html(createFormulaHTML(formulaAsJson, true));
        $li.append($span);

        // Add event (click, ...)
        let possibleRules = getRules(formulaAsJson);
        for (let ruleEvent of possibleRules) {
            let $spanForEvent = $li.find('span.' + ruleEvent.element).first();
            if (ruleEvent.onclick.length === 1) {
                // Single click
                let rule = ruleEvent.onclick[0];
                $spanForEvent.on('click', buildApplyRuleCallBack(rule, $li));

                // Some hover config for tensor
                if (rule === 'tensor') {
                    $li.addClass('tensor');
                    let $rightFormula = $li.find('span' + '.right-formula').first();
                    $rightFormula.addClass('tensor-right');
                }
            } else {
                // Single click AND Double click event
                let singleClickCallBack = buildApplyRuleCallBack(ruleEvent.onclick[0], $li);
                let doubleClickCallBack = buildApplyRuleCallBack(ruleEvent.onclick[1], $li);

                // https://stackoverflow.com/a/7845282
                $spanForEvent.on('click', function () {
                    clickCount++;
                    if (clickCount === 1) {
                        window.clickTimer = setTimeout(function () {
                            singleClickCallBack();
                            window.clickCount = 0;
                        }, CLICK_DELAY);
                    } else {
                        clearTimeout(window.clickTimer);
                        doubleClickCallBack();
                        window.clickCount = 0;
                    }
                })
            }

            // Some hover config
            $spanForEvent.addClass('clickableExpr');
            if (ruleEvent.element !== 'main-formula') {
                $spanForEvent.addClass('highlightableExpr');
            }
        }

        $ul.append($li);
    }
    $sequentDiv.append($ul);
}

function createFormulaHTML(formulaAsJson, isMainFormula = true) {
    switch (formulaAsJson.type) {
        case 'litteral':
            return `<span>${formulaAsJson.value}</span>`;

        case 'neutral':
            let neutralElement = NEUTRAL_ELEMENTS[formulaAsJson.value];
            if (isMainFormula) {
                return `<span class="primaryConnector">${neutralElement}</span>`;
            }
            return neutralElement;

        case 'negation':
            return UNARY_CONNECTORS[formulaAsJson.type] + createFormulaHTML(formulaAsJson.value, false);

        case 'ofcourse':
        case 'whynot':
            let unaryConnector = UNARY_CONNECTORS[formulaAsJson.type];
            let subFormula = createFormulaHTML(formulaAsJson.value, false);
            if (isMainFormula) {
                unaryConnector = `<span class="primaryConnector">${unaryConnector}</span>`;
                subFormula = `<span class="sub-formula">${subFormula}</span>`;
            }
            return unaryConnector + subFormula;

        case 'orthogonal':
            return createFormulaHTML(formulaAsJson.value, false)
                + '<span><sup>⊥</sup></span>';

        case 'implication':
        case 'conjunction':
        case 'disjunction':
        case 'tensor':
        case 'par':
        case 'with':
        case 'plus':
        case 'lollipop':
            let connector = BINARY_CONNECTORS[formulaAsJson.type];
            if (isMainFormula) {
                connector = `<span class="primaryConnector">${connector}</span>`;
            }

            let leftFormula = createFormulaHTML(formulaAsJson['value1'], false);
            let rightFormula = createFormulaHTML(formulaAsJson['value2'], false);
            if (isMainFormula) {
                leftFormula = `<span class="left-formula">${leftFormula}</span>`;
                rightFormula = `<span class="right-formula">${rightFormula}</span>`;
            }
            let formula = leftFormula + connector + rightFormula;

            if (!isMainFormula) {
                return `<span>(</span>${formula}<span>)</span>`;
            }

            return formula;

        default:
            console.error('No display rule for type ' + formulaAsJson.type);
            return '';
    }
}

// ************
// PROOF UPDATE
// ************

function addSequentListPremisses($sequentDiv, sequentList, rule) {
    // Save rule
    $sequentDiv.data('rule', rule);

    // Add line
    let $td = $sequentDiv.closest('td');
    $td.addClass('inference');

    // Add rule symbol
    $td.next('.tagBox')
        .html($('<div>', {'class': 'tag'})
            .html(RULES[rule]));

    // Remove old premisses if any
    let $table = $td.closest('table');
    $table.prevAll().each(function (i, e) {
        e.remove();
    });

    // Mark proof as incomplete
    markAsIncomplete();

    // Add new sequents
    if (sequentList.length === 0) {
        checkProofIsComplete();
    } else if (sequentList.length === 1) {
        createSequentTable(sequentList[0]).insertBefore($table);
    } else {
        let $div = $('<div>');
        for (let sequent of sequentList) {
            let $sibling = $('<div>', {'class': 'sibling'})
            $sibling.append(createSequentTable(sequent))
            $div.append($sibling);
        }
        $div.insertBefore($table);
    }
}

// **********
// OPERATIONS
// **********

function getRules(formulaAsJson) {
    switch (formulaAsJson.type) {
        case 'litteral':
        case 'orthogonal':
            return [{'element': 'main-formula', 'onclick': ['axiom']}];

        case 'tensor':
        case 'par':
        case 'with':
            return [{'element': 'main-formula', 'onclick': [formulaAsJson.type]}];

        case 'plus':
            return [
                {'element': 'left-formula', 'onclick': ['plus_left']},
                {'element': 'right-formula', 'onclick': ['plus_right']}
            ];

        case 'neutral':
            switch (formulaAsJson.value) {
                case 'one':
                case 'top':
                case 'bottom':
                case 'zero': // click on zero will display a pedagogic error
                    return [{'element': 'main-formula', 'onclick': [formulaAsJson.value]}];

                default:
                    return [];
            }

        case 'ofcourse':
            return [{'element': 'main-formula', 'onclick': ['promotion']}];

        case 'whynot':
            return [
                {'element': 'primaryConnector', 'onclick': ['weakening']},
                {'element': 'sub-formula', 'onclick': ['dereliction', 'contraction']}
            ];

        default:
            return [];
    }
}

function buildApplyRuleCallBack(rule, $li) {
    return function() {
        let $sequentDiv = $li.closest('div.sequent');
        let formulaPosition = $li.parent().children().index($li);

        applyRule(rule, $sequentDiv, formulaPosition);
    }
}

function applyRule(rule, $sequentDiv, formulaPosition) {
    let sequent = getSequentWithPermutations($sequentDiv);

    $.ajax({
        type: 'POST',
        url: '/apply_rule',
        contentType:'application/json; charset=utf-8',
        data: JSON.stringify({ rule, sequent, formulaPosition }),
        success: function(data)
        {
            console.log(data);
            if (data.success === true) {
                cleanPedagogicError();
                addSequentListPremisses($sequentDiv, data['sequentList'], rule);
            } else {
                displayPedagogicError(data['errorMessage']);
            }
        },
        error: function(jqXHR, textStatus, errorThrown) {
            console.log(jqXHR);
            console.log(jqXHR.responseText);
            console.log(textStatus);
            console.log(errorThrown);
            alert('Technical error, check browser console for more details.');
        }
    });
}

function getSequentWithPermutations($sequentDiv) {
    let sequent = $sequentDiv.data('sequent');

    return {
        'hyp': getFormulasWithPermutation($sequentDiv.find('ul.hyp'), sequent['hyp']),
        'cons': getFormulasWithPermutation($sequentDiv.find('ul.cons'), sequent['cons'])
    };
}

function getFormulasWithPermutation($ul, initialFormulas) {
    let newFormulas = [];

    $ul.find('li').each(function(i, obj) {
        let initialPosition = $(obj).data('initialPosition');
        newFormulas.push(initialFormulas[initialPosition]);
    })

    return newFormulas;
}

// ************
// GLOBAL PROOF
// ************

function checkProofIsComplete() {
    let $mainDiv = $('#main-proof-container')
        .children('div');
    let $mainTable = $mainDiv.children('div.proof')
        .children('table').last();
    if (recCheckIsComplete(recGetProofAsJson($mainTable))) {
        $mainDiv.removeClass('proofIsIncomplete');
        $mainDiv.addClass('proofIsDone');
    }
}

function recGetProofAsJson($table) {
    let $sequentDiv = $table.find('div.sequent');
    let sequent = $sequentDiv.data('sequent');
    let rule = $sequentDiv.data('rule') || null;
    let premisses = [];
    if (rule !== null) {
        let $prev = $table.prev();
        if ($prev.length) {
            if ($prev.prop('tagName') === 'TABLE') {
                premisses = [recGetProofAsJson($prev)];
            } else {
                $prev.children('div.sibling').each(function (i, sibling) {
                    premisses.push(recGetProofAsJson($(sibling).children('table')));
                })
            }
        }
    }

    return { sequent, rule, premisses };
}

function recCheckIsComplete(proofAsJson) {
    if (proofAsJson.rule === null) {
        return false;
    }

    let response = true;

    for (let premiss of proofAsJson.premisses) {
        response = response && recCheckIsComplete(premiss);
    }

    return response;
}

function markAsIncomplete() {
    let $mainDiv = $('#main-proof-container')
        .children('div');
    $mainDiv.removeClass('proofIsDone');
    $mainDiv.addClass('proofIsIncomplete');
}
