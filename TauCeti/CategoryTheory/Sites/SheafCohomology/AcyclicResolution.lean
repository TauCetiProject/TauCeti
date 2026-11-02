/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence
import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Vanishing cohomology and sections of acyclic resolutions

Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F` on a site, and let
`V` be an object of the site over which every term `Kʲ` has no cohomology in positive degrees,
for instance because each `Kʲ` is injective, or flasque on a topological space. Then the complex
of sections `K⁰(V) ⟶ K¹(V) ⟶ ⋯` computes the cohomology `Hⁿ(V, F)`. This file proves the half of
this statement that is used to show that derived functors vanish: if `Hⁿ⁺¹(V, F) = 0`, then the
complex of sections is exact in degree `n + 1`
(`CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`).

The proof is the classical dimension shift. Write `Zʲ` for the cycles of `K` in degree `j`. The
resolution splits into short exact sequences `0 ⟶ F ⟶ K⁰ ⟶ Z¹ ⟶ 0` and
`0 ⟶ Zʲ ⟶ Kʲ ⟶ Zʲ⁺¹ ⟶ 0`, and the long exact cohomology sequences over `V` give
`Hᵏ(V, Zʲ⁺¹) = 0` whenever `Hᵏ⁺¹(V, Zʲ) = 0` and `k ≥ 1`. Starting from `Hⁿ⁺¹(V, F) = 0`, this
gives `H¹(V, Zⁿ) = 0`, so that `Kⁿ(V) ⟶ Zⁿ⁺¹(V)` is surjective: every cycle of `K(V)` in degree
`n + 1` is a boundary.

## Main declarations

* `CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`: if `Hⁿ⁺¹(V, F) = 0` and the terms
  of a resolution `K` of `F` are acyclic over `V`, then every cycle of `K(V)` in degree `n + 1` is
  a boundary.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A.
-/

public section

open CategoryTheory Limits Opposite Abelian

universe w v u

namespace CategoryTheory

namespace Sheaf

namespace H'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  {F : Sheaf J AddCommGrpCat.{v}} {K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] (ι : F ⟶ K.X 0) [Mono ι] (hι : ι ≫ K.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (K.d 0 1) hι).Exact) (hK : ∀ j, K.ExactAt (j + 1)) (V : C)
  (hKV : ∀ j k, Subsingleton ((K.X j).H' (k + 1) V))

include hι' hK hKV in
/-- Dimension shifting along the resolution: `Hᵏ⁺¹(V, Zʲ⁺¹)` vanishes when
`Hʲ⁺ᵏ⁺²(V, F)` does. -/
private lemma subsingleton_H'_cycles (j k : ℕ) (hF : Subsingleton (F.H' (j + k + 2) V)) :
    Subsingleton ((K.cycles (j + 1)).H' (k + 1) V) := by
  induction j generalizing k with
  | zero =>
    rw [zero_add] at hF
    exact subsingleton_X₃ (K.shortExact_toCycles ι hι hι' (by simp) (hK 0)) V (k + 1)
      (hKV 0 k) hF
  | succ j ih =>
    have hS := K.cyclesShortComplex_shortExact (j + 1) (j + 2) (by simp) (hK (j + 1))
    rw [HomologicalComplex.cyclesShortComplex_def] at hS
    exact subsingleton_X₃ hS V (k + 1) (hKV (j + 1) k)
      (ih (k + 1) (by rwa [show j + (k + 1) + 2 = j + 1 + k + 2 by omega]))

include hι' hK hKV in
/-- **Exactness of sections of an acyclic resolution**, in the form used to show that derived
functors vanish. Let `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be a resolution of a sheaf of abelian groups `F`
whose terms have no cohomology in positive degrees over an object `V` of the site. If
`Hⁿ⁺¹(V, F) = 0`, then every section of `Kⁿ⁺¹` over `V` killed by the differential is the image
of a section of `Kⁿ` over `V`: the complex of sections `K(V)` is exact in degree `n + 1`. -/
theorem exists_d_hom_app_eq_of_resolution (n : ℕ) (hF : Subsingleton (F.H' (n + 1) V))
    (s : (K.X (n + 1)).obj.obj (op V)) (hs : (K.d (n + 1) (n + 2)).hom.app (op V) s = 0) :
    ∃ t : (K.X n).obj.obj (op V), (K.d n (n + 1)).hom.app (op V) t = s := by
  -- `s` is a section of the cycles `Zⁿ⁺¹`, the kernel of the differential
  have hZ : (ShortComplex.mk (K.iCycles (n + 1)) (K.d (n + 1) (n + 2))
      (K.iCycles_d _ _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp))
  obtain ⟨z, rfl⟩ := (ShortComplex.ab_exact_iff _).1
    (hZ.map_of_mono_of_preservesKernel (sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V)) inferInstance inferInstance) s hs
  -- `Kⁿ(V) ⟶ Zⁿ⁺¹(V)` is onto, since `H¹(V, F) = 0` for `n = 0` and `H¹(V, Zⁿ) = 0` otherwise
  obtain ⟨t, rfl⟩ : ∃ t, (K.toCycles n (n + 1)).hom.app (op V) t = z := by
    cases n with
    | zero =>
      exact g_hom_app_surjective (K.shortExact_toCycles ι hι hι' (by simp) (hK 0)) V hF z
    | succ n =>
      have hS := K.cyclesShortComplex_shortExact (n + 1) (n + 2) (by simp) (hK (n + 1))
      rw [HomologicalComplex.cyclesShortComplex_def] at hS
      exact g_hom_app_surjective hS V
        (subsingleton_H'_cycles ι hι hι' hK V hKV n 0 hF) z
  refine ⟨t, ?_⟩
  -- the mapped inclusion of cycles is by definition the component of `iCycles` at `V`
  rw [← K.toCycles_i n (n + 1)]
  rfl

end H'

end Sheaf

end CategoryTheory
