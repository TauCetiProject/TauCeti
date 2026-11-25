/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.RingTheory.MatlisDuality.Indecomposable

/-!
# The Auslander--Reiten translate

Let `A` be an algebra over a commutative ring `R`, and `E` an `R`-module.  The **Matlis dual**
`D = Hom_R(-, E)` turns a right `A`-module into a left `A`-module (`TauCeti.MatlisDual`).  This file
applies that duality to the Auslander--Reiten transpose to define the **Auslander--Reiten
translate**

`τ M = D (Tr M)`

of a module `M` presented by a minimal projective presentation `P₁ → P₀ → M → 0`, the Matlis dual
of the Auslander--Reiten transpose `TauCeti.AuslanderReitenTranspose` of that presentation.  The
transpose is a right `A`-module, so the translate is a left `A`-module again, as `M` was.

For an Artin algebra, `E` is an injective hull of `R ⧸ J(R)`; for an algebra over a field `k`, it is
`k` itself, and `τ = Hom_k(Tr -, k)` is the classical translate.  Both are the one construction
`TauCeti.AuslanderReitenTranslate R E`.

The translate is attached to a *presentation*, not directly to `M`: like the transpose it is
well defined only because a minimal projective presentation is unique up to isomorphism of the whole
diagram.  `TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranslate` is
that statement, and it is what licenses the notation `τ M`.

## Main definitions

* `TauCeti.AuslanderReitenTranslate R E`: the Matlis dual `D (Tr)` of the Auslander--Reiten
  transpose of a linear map `p₁ : P₁ → P₀`, carrying the resulting `A`-module structure.  It is the
  Auslander--Reiten translate of `M` when `p₁` is the first map of a minimal projective presentation
  of `M`.

## Main results

* `TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranslate`: the
  translate is independent, up to `A`-linear equivalence, of the chosen minimal projective
  presentation.
* `TauCeti.IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranslate_of_projective`: the
  translate of a projective module vanishes.
* `TauCeti.IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranslate_iff_projective`:
  for a finitely generated left-hand source and an injective cogenerator `E`, the converse holds
  too — **the translate vanishes exactly on the projective modules** — so that `τ` assigns a
  nonzero module to every non-projective one.
* The translate is the Matlis dual of the transpose, so
  `TauCeti.MatlisDual.isIndecomposableModule_iff` shows that, when the transpose has finite length
  over `R`, the translate is indecomposable exactly when the transpose is.

## Implementation notes

The translate is a reducible abbreviation of `TauCeti.MatlisDual`, so that the whole Matlis duality
API applies to it unchanged: its `A`-action is `TauCeti.MatlisDual.smul_apply`, its transport along
an isomorphism of transposes is `TauCeti.MatlisDual.congrOp`, and biduality, faithfulness and the
exchange of projectives and injectives are those of `TauCeti/RingTheory/MatlisDuality/`.  Over a
field `k` the elements of `AuslanderReitenTranslate k k p₁` are `k`-linear functionals on the
transpose through `TauCeti.MatlisDual.equivLinearMap`.

The shorter name `arTranslate` is used for the translate of a *module*, `ModuleCat.arTranslate`,
which chooses a minimal presentation.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Section IV.2.
-/

public section

namespace TauCeti

universe u v v' w w' x y

variable {A : Type u} [Ring A]

section Translate

variable {P₀ : Type v} {P₁ : Type w} [AddCommMonoid P₀] [Module A P₀]
  [AddCommMonoid P₁] [Module A P₁]

/-- The **Auslander--Reiten translate** `τ = D Tr` attached to a linear map `p₁ : P₁ → P₀`: the
Matlis dual `D_R = Hom_R(-, E)` of its Auslander--Reiten transpose.  The transpose is a right
`A`-module, so its Matlis dual is a left `A`-module.

When `p₁` is the first map of a minimal projective presentation `P₁ → P₀ → M → 0`, this is the
Auslander--Reiten translate of `M`: no exactness or projectivity is needed to form it, and
minimality enters only through
`TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_auslanderReitenTranslate`, which shows
that the result is then independent, up to equivalence, of the chosen presentation. -/
abbrev AuslanderReitenTranslate (R : Type x) [CommRing R] [Algebra R A] (E : Type y)
    [AddCommGroup E] [Module R E] (p₁ : P₁ →ₗ[A] P₀) : Type _ :=
  MatlisDual R E (AuslanderReitenTranspose p₁)

end Translate

variable {R : Type x} [CommRing R] [Algebra R A] {E : Type y} [AddCommGroup E] [Module R E]

namespace IsMinimalProjectivePresentation

variable {M : Type*} [AddCommGroup M] [Module A M]
variable {P₀ : Type v} [AddCommGroup P₀] [Module A P₀]

section Projective

variable {P₁ : Type w} [AddCommMonoid P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- The Auslander--Reiten translate of a projective module vanishes: its transpose already does,
and the dual of a subsingleton is a subsingleton. -/
theorem subsingleton_auslanderReitenTranslate_of_projective [Module.Projective A M]
    (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (AuslanderReitenTranslate R E p₁) :=
  let _ : Subsingleton (AuslanderReitenTranspose p₁) :=
    h.subsingleton_auslanderReitenTranspose_of_projective
  (MatlisDual.equivLinearMap R E _).toEquiv.subsingleton

end Projective

section Vanishing

variable {P₁ : Type w} [AddCommGroup P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- **The Auslander--Reiten translate vanishes exactly on the projective modules**, for a
minimal projective presentation with finitely generated left-hand source and an injective `E`
that receives a nonzero map from every simple `R`-module.  This is what makes `τ` a construction
on the *non-projective* modules: it assigns a nonzero module to every module that is not
projective.

No finiteness over `R` is needed: such an `E` is a cogenerator, so the Matlis dual of the
transpose vanishes only when the transpose does (`TauCeti.subsingleton_matlisDual_iff`).  The
implication the other way — a projective `M` has vanishing translate — is
`TauCeti.IsMinimalProjectivePresentation.subsingleton_auslanderReitenTranslate_of_projective`, and
needs no hypothesis on `E`. -/
theorem subsingleton_auslanderReitenTranslate_iff_projective [Module.Injective R E]
    [Small.{y} R] (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Nontrivial (R ⧸ 𝔪 →ₗ[R] E))
    [Module.Finite A P₁] (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (AuslanderReitenTranslate R E p₁) ↔ Module.Projective A M :=
  (subsingleton_matlisDual_iff hE).trans h.subsingleton_auslanderReitenTranspose_iff_projective

end Vanishing

section Comparison

variable {P₁ : Type w} [AddCommGroup P₁] [Module A P₁]
variable {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}
variable {Q₀ : Type v'} {Q₁ : Type w'} [AddCommGroup Q₀] [Module A Q₀]
  [AddCommGroup Q₁] [Module A Q₁]
variable {q₁ : Q₁ →ₗ[A] Q₀} {q₀ : Q₀ →ₗ[A] M}

/-- **The Auslander--Reiten translate is well defined**: it is independent, up to `A`-linear
equivalence, of the chosen minimal projective presentation of a module.  This is the statement that
licenses writing `τ M` for a module `M`. -/
theorem nonempty_linearEquiv_auslanderReitenTranslate (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) :
    Nonempty (AuslanderReitenTranslate R E p₁ ≃ₗ[A] AuslanderReitenTranslate R E q₁) :=
  (h'.nonempty_linearEquiv_auslanderReitenTranspose h).map MatlisDual.congrOp

end Comparison

end IsMinimalProjectivePresentation

end TauCeti
