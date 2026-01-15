!define(ref)
~~~~~~~~~~~~
[`` !ifne(!2)()(!2)(!1) ``](#!ifne(!2)()(!1.!2)(!1))
~~~~~~~~~~~~

!define(remoteRef)
~~~~~~~~~~~~
[`` !ifne(!4)()(!4)(!3) ``](../../!1/!2#!ifne(!4)()(!3.!4)(!3))
~~~~~~~~~~~~

!define(chapterRef)
~~~~~~~~~~~~
[Ch. !1/!2](../../!1/!2)
~~~~~~~~~~~~

!define(flexRef)
~~~~~~~~~~~~
[!4](../../!1/!2#!3)
~~~~~~~~~~~~

!define(refExercise)
~~~~~~~~~~~~~
[Exercise %g](!1 "Exercise %g")
~~~~~~~~~~~~~

!define(refSection)
~~~~~~~~~~~~~
[this section](!1 "Section %g")
~~~~~~~~~~~~~

!define(standardPreamble)
~~~~~~~~~~~~~~~~~
module !part().!chapter().!1 where
open import TypeOf
open import !part().!chapter() renaming (!2 to !2-orig)
~~~~~~~~~~~~~~~~~

!define(standardPreamble2)
~~~~~~~~~~~~~~~~~
module !part().!chapter().!1 where
open import TypeOf
open import !part().!chapter() renaming (!2 to !2-orig; !3 to !3-orig)
~~~~~~~~~~~~~~~~~

!define(preamble)
~~~~~~~~~~~~~~~~~
!standardPreamble(!1)(!2)
~~~~~~~~~~~~~~~~~

!define(preamble2)
~~~~~~~~~~~~~~~~~
!standardPreamble2(!1)(!2)(!3) 
~~~~~~~~~~~~~~~~~

// the extra newlines below are significant
!define(codemirrorCustom)
~~~~~~~~~~~~~~~~~~~~

<pre data-executable="true" data-language="agda" id="!part().!chapter().!1">
!2
</pre>

~~~~~~~~~~~~~~~~~~~~

!define(codemirror)
~~~~~~~~~~~~~~~~~~~~
!codemirrorCustom(!1)
~~~~~~~~~
!define(name)(!ifne(!2)()(!2)(!1))
!define(code)
~~~
!preamble(!1)(!name)
!name : typeOf !name-orig

-- BEGIN SOLUTION
!name = ?
~~~
!code
!comment
~~~
!define(dirname)(src/!part()/!chapter())
!define(filename)(!dirname/!1.agda)
!exec(mkdir -p !dirname)
!exec(touch !filename)
!lit(!filename)()(!code)
~~~
~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~

!define(codemirror2)
~~~~~~~~~~~~~~~~~~~~
!codemirrorCustom(!1)
~~~~~~~~~
!preamble2(!1)(!2)(!3)
!2 : typeOf !2-orig
!3 : typeOf !3-orig

-- BEGIN SOLUTION
!2 = ?
!3 = ?
~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~

!define(exercise)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::::: {.exercisebox}

!ifne(!4)()(Exercise (!2) !1)(Exercise !1)
: !ifne(!4)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>

<!--
::::::: {.solutionlink}
[solution](!1-solution)
:::::::
-->

:::::

!append(solutions)
``````````````````

::::: {.solutionbox}

###### Solution to [Exercise %g](!1 "Exercise %g") {!1-solution}

!ifne(!4)()(!4)(!3)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
``````````````````
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(example)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.examplebox}
Example !1
: !2 <span class="hidden">∎</span><span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(theorem)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.theorembox}

!ifne(!3)()(Theorem (!2))(Theorem) !1
: !ifne(!3)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(lemma)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.lemmabox}

!ifne(!3)()(Lemma (!2))(Lemma) !1
: !ifne(!3)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(remark)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
::::: {.remarkbox}

!ifne(!3)()(Remark (!2))(Remark) !1
: !ifne(!3)()(!3)(!2)
<span class="hidden">∎</span>
<span class="right-aligned">∎</span>
:::::
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(hide)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::::: {.introbox}

!1 <button type="button" class="hidden">[show]</button> <button type="button" class="collapsible">[show]</button>

:::::

::::: {.hidebox}

!2

:::::

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!define(solutionsSection)
~~~~~~~~~~~~~~~~~~~~~~
!ifdef(solutions)
~~~~~~~~~~~
# Solutions

!solutions

----------
~~~~~~~~~~~
~~~~~~~~~~~
~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~