/************************************************************************/
/*         *      The Rocq Prover / The Rocq Development Team           */
/*  v      *         Copyright INRIA, CNRS and contributors             */
/* <O___,, * (see version control and CREDITS file for authors & dates) */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/
function annotateSup(marker) {
    switch (marker) {
    case "?":
        return "This block is optional.";
    case "*":
        return "This block is optional, and may be repeated.";
    case "+":
        return "This block may be repeated.";
    }
}

function annotateSub(separator) {
    return "Use “" + separator + "” to separate repetitions of this block.";
}

// function translatePunctuation(original) {
//     var mappings = { ",": "⸴" }; // ，
//     return mappings[original] || original;
// }

function annotateNotations () {
    $(".repeat-wrapper > sup")
        .attr("data-hint", function() {
            return annotateSup($(this).text());
        }).addClass("hint--top hint--rounded");

    $(".repeat-wrapper > sub")
        .attr("data-hint", function() {
            return annotateSub($(this).text());
        }).addClass("hint--bottom hint--rounded");
    //.text(function(i, text) { return translatePunctuation(text); });
}

$(annotateNotations);
