/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Mayer-Vietoris for the cohomology of a sheaf of modules on a scheme

`TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` defines the cohomology `Hⁿ(X, M)` of a sheaf of
modules on a scheme, and the cohomology `Hⁿ(U, M)` of an open subset. This file adds the long
exact Mayer-Vietoris sequence of two open subsets `U` and `V`:

`⋯ ⟶ Hⁿ(U ⊔ V, M) ⟶ Hⁿ(U, M) ⊞ Hⁿ(V, M) ⟶ Hⁿ(U ⊓ V, M) ⟶ Hⁿ⁺¹(U ⊔ V, M) ⟶ ⋯`

together with the vanishing it gives when `U` and `V` cover `X`.

## Main declarations

* `Scheme.Modules.mayerVietorisSequence` is the six-term piece of the long exact sequence,
  `Scheme.Modules.mayerVietorisSequence_def` identifies each of its objects and arrows with
  restriction maps and the connecting map `Scheme.Modules.mayerVietorisδ`, and
  `Scheme.Modules.mayerVietorisSequence_exact` is its exactness;
* `Scheme.Modules.epi_mayerVietorisδ`: if `Hⁿ⁺¹(U, M)` and `Hⁿ⁺¹(V, M)` vanish, then the
  connecting map `Hⁿ(U ⊓ V, M) ⟶ Hⁿ⁺¹(U ⊔ V, M)` is an epimorphism;
* `Scheme.Modules.subsingleton_cohomologyOn_sup_succ`: if moreover `Hⁿ(U ⊓ V, M)` vanishes,
  then `Hⁿ⁺¹(U ⊔ V, M)` vanishes; `Scheme.Modules.subsingleton_cohomology_succ` specializes
  this to `Hⁿ⁺¹(X, M)` when `U ⊔ V = ⊤`, and
  `Scheme.Modules.subsingleton_cohomology_of_two_le` applies this at degree `n - 1` under
  uniform positive-degree acyclicity hypotheses;
* `Scheme.Modules.subsingleton_cohomology_of_two_le_of_isAffineOpen` applies affine-open
  acyclicity when `U`, `V`, and `U ⊓ V` are affine, while the `_of_isAffineHom` variant obtains
  the intersection hypothesis from an affine diagonal.

These statements are the shape in which Mayer-Vietoris is used on a curve. The general theorem
accepts arbitrary coefficients and explicit acyclicity hypotheses. For quasi-coherent
coefficients on a locally Noetherian scheme, the affine-open variants use the acyclicity of
quasi-coherent sheaves on affine opens; users may either supply an affine intersection directly
or obtain it from an affine diagonal.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: … vanishing above dimension (`H² = 0` on a curve)". No formalization is
vendored: the long exact sequence is Mathlib's
`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact`, the square attached to
two open subsets is Mathlib's `TopologicalSpace.Opens.mayerVietorisSquare`, and the comparison
between the cohomology of the terminal open subset and the cohomology of the site comes from
`TauCeti/CategoryTheory/Sites/SheafCohomology/Terminal.lean` through
`Scheme.Modules.cohomologyOnTopIso`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

section MayerVietoris

variable (U V : Opens X)

/-- The connecting map `Hⁿ⁰(U ⊓ V, M) ⟶ Hⁿ¹(U ⊔ V, M)` of the Mayer-Vietoris sequence of two
open subsets. -/
noncomputable abbrev mayerVietorisδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyOn M n₀ (U ⊓ V) ⟶ cohomologyOn M n₁ (U ⊔ V) :=
  (Opens.mayerVietorisSquare U V).δ
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n₀ n₁ h

/-- Six consecutive terms of the Mayer-Vietoris long exact sequence of two open subsets, running
from `Hⁿ⁰(U ⊔ V, M)` to `Hⁿ¹(U ⊓ V, M)`. -/
noncomputable abbrev mayerVietorisSequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (Opens.mayerVietorisSquare U V).sequence
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n₀ n₁ h

/-- Every object and every arrow of the Mayer-Vietoris sequence: the two maps to a biproduct are
the pairs of restriction maps from `U ⊔ V`, the two maps out of a biproduct are the differences of
the restriction maps to `U ⊓ V`, and the middle map is the connecting map. -/
@[simp]
lemma mayerVietorisSequence_def (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    mayerVietorisSequence M U V n₀ n₁ h =
      ComposableArrows.mk₅
        (biprod.lift (cohomologyOnRes M n₀ (le_sup_left : U ≤ U ⊔ V))
          (cohomologyOnRes M n₀ (le_sup_right : V ≤ U ⊔ V)))
        (biprod.desc (cohomologyOnRes M n₀ (inf_le_left : U ⊓ V ≤ U))
          (-cohomologyOnRes M n₀ (inf_le_right : U ⊓ V ≤ V)))
        (mayerVietorisδ M U V n₀ n₁ h)
        (biprod.lift (cohomologyOnRes M n₁ (le_sup_left : U ≤ U ⊔ V))
          (cohomologyOnRes M n₁ (le_sup_right : V ≤ U ⊔ V)))
        (biprod.desc (cohomologyOnRes M n₁ (inf_le_left : U ⊓ V ≤ U))
          (-cohomologyOnRes M n₁ (inf_le_right : U ⊓ V ≤ V))) :=
  -- This is definitional after unfolding Mathlib's `toBiprod` and `fromBiprod` together with
  -- the four structure maps of `Opens.mayerVietorisSquare`.
  rfl

/-- The Mayer-Vietoris sequence of two open subsets is exact. -/
theorem mayerVietorisSequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mayerVietorisSequence M U V n₀ n₁ h).Exact :=
  (Opens.mayerVietorisSquare U V).sequence_exact _ _ _ _

/-- If the degree `n + 1` cohomology of both of two open subsets vanishes, then the Mayer-Vietoris
connecting map onto `Hⁿ⁺¹(U ⊔ V, M)` is an epimorphism. -/
theorem epi_mayerVietorisδ (n : ℕ)
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Epi (mayerVietorisδ M U V n (n + 1) rfl) :=
  (Opens.mayerVietorisSquare U V).epi_δ
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n + 1) rfl hU hV

variable {U V}

/-- If the degree `n + 1` cohomology of both of two open subsets vanishes, and their intersection
has vanishing degree `n` cohomology, then their union has vanishing degree `n + 1` cohomology. -/
theorem subsingleton_cohomologyOn_sup_succ (n : ℕ)
    (hInter : Subsingleton (cohomologyOn M n (U ⊓ V)))
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Subsingleton (cohomologyOn M (n + 1) (U ⊔ V)) :=
  (Opens.mayerVietorisSquare U V).subsingleton_H'_X₄
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n + 1) rfl hInter hU hV

/-- A scheme covered by two open subsets whose degree `n + 1` cohomology vanishes, and whose
intersection has vanishing degree `n` cohomology, has vanishing degree `n + 1` cohomology. -/
theorem subsingleton_cohomology_succ (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hInter : Subsingleton (cohomologyOn M n (U ⊓ V)))
    (hU : Subsingleton (cohomologyOn M (n + 1) U))
    (hV : Subsingleton (cohomologyOn M (n + 1) V)) :
    Subsingleton (Cohomology M (n + 1)) := by
  have hTop := subsingleton_cohomologyOn_sup_succ M n hInter hU hV
  rw [hUV] at hTop
  exact (cohomologyOnTopIso M (n + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- A scheme covered by two open subsets which, together with their intersection, are acyclic in
positive degrees has no cohomology in degrees at least two.

This is the form Mayer-Vietoris takes on a separated scheme covered by two affine opens: the
intersection is then affine as well. For quasi-coherent `M` on a locally Noetherian scheme the
hypotheses are the acyclicity of quasi-coherent sheaves on affine opens, which gives
`Scheme.Modules.subsingleton_cohomology_of_two_le_of_isAffineOpen`; for a general
`M : X.Modules` they have to come from elsewhere. -/
theorem subsingleton_cohomology_of_two_le (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n)
    (hU : ∀ i, 0 < i → Subsingleton (cohomologyOn M i U))
    (hV : ∀ i, 0 < i → Subsingleton (cohomologyOn M i V))
    (hInter : ∀ i, 0 < i → Subsingleton (cohomologyOn M i (U ⊓ V))) :
    Subsingleton (Cohomology M n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact subsingleton_cohomology_succ M hUV m (hInter m (by omega)) (hU _ (by omega))
    (hV _ (by omega))

end MayerVietoris

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : Scheme.{u}} (M : X.Modules)

/-- A quasi-coherent sheaf of modules on a locally Noetherian scheme covered by two affine opens
with affine intersection has no cohomology in degrees at least two. -/
theorem subsingleton_cohomology_of_two_le_of_isAffineOpen [IsLocallyNoetherian X]
    [M.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hInter : IsAffineOpen (U ⊓ V)) (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology M n) := by
  have hacyclic {W : X.Opens} (hW : IsAffineOpen W) (i : ℕ) (hi : 0 < i) :
      Subsingleton (cohomologyOn M i W) := by
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact subsingleton_cohomologyOn_succ_of_isAffineOpen M hW j
  exact subsingleton_cohomology_of_two_le M hUV n hn (hacyclic hU) (hacyclic hV)
    (hacyclic hInter)

/-- A quasi-coherent sheaf of modules on a locally Noetherian scheme with affine diagonal (for
instance a separated one) that is covered by two affine opens has no cohomology in degrees at
least two. -/
theorem subsingleton_cohomology_of_two_le_of_isAffineOpen_of_isAffineHom
    [IsLocallyNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [M.IsQuasicoherent] {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) :=
  subsingleton_cohomology_of_two_le_of_isAffineOpen M hU hV (hU.inf hV) hUV n hn

end

end AlgebraicGeometry.Scheme.Modules
