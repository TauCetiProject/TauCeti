/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
import TauCeti.Data.DFinsupp.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import TauCeti.NumberTheory.ClassFieldTheory.Global.ClassFormation
import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftIndependence
import TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant

/-!
# Exactness of the global Brauer sequence at the local Brauer groups

Let `K` be a number field. This file proves that the global Brauer sequence

```text
0 → Br K → ⨁_v Br K_v → ℚ/ℤ → 0
```

is exact at `⨁_v Br K_v`: a family of local Brauer classes is the family of localizations of a
global Brauer class exactly when its local invariants sum to zero (`range_brLocalization`). In
invariant coordinates (`exists_br_of_sum_eq_zero`): a finitely supported family of elements of
`ℚ/ℤ` at the finite places, together with elements killed by `2` at the real places and `0` at the
complex places, is the family of local invariants of a global Brauer class when its sum is zero.
These are exactly the conditions satisfied by the local invariants of a global class
(`hasFiniteSupport_finiteInvAt`, `infiniteInvAt_mem_torsionBy_two`,
`infiniteInvAt_eq_zero_of_isComplex` and `sumLocalInv_brLocalization_eq_zero`). With the Hasse
principle `brLocalization_injective`, a Brauer class of `K` is thus determined by its local
invariants, and every admissible family of invariants occurs.

That the sum of the local invariants of a localized class vanishes is
`sumLocalInv_brLocalization_eq_zero`. Conversely, every family `y` of local Brauer classes is the
family of localizations of a class `z ∈ H²(G_K, I_{Kˢ})` of the ideles
(`ideleLocalization_surjective`), and `z` is the class over `G_K` of a class `z'` of the idele
cohomology of some layer `V ◁ G_K` (`exists_refinement_ideleLayerCorInfl_eq_index_nsmul`, the
index of `G_K` in itself being `1`). If the local invariants of `y` sum to zero, then `z'` dies in
the cohomology of the idele classes (`ideleToClassH2_eq_zero_iff`), so it comes from
`H²(Gal(L/K), Lˣ)` by exactness of `Lˣ → I_L → C_L` (`ker_ideleToClassH2`). Its image in `Br K`
then localizes to `y` (`ideleLayerCorInfl_multiplicativeToIdeleH2`,
`ideleLocalization_principalIdele`).

## Main results

* `TauCeti.ClassFieldTheory.range_brLocalization`: the image of `Br K → ⨁_v Br K_v` is the kernel
  of the sum of the local invariants.
* `TauCeti.ClassFieldTheory.exists_br_of_sum_eq_zero`: a family of local invariants that is
  finitely supported, killed by `2` at the real places, zero at the complex places, and of sum
  zero, is the family of local invariants of a global Brauer class.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 4.2.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (8.1.17).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField

variable (K : Type) [Field K] [NumberField K]

/-- **Exactness of the global Brauer sequence at `⨁_v Br K_v`**: a family of local Brauer classes
is the family of localizations of a global Brauer class exactly when its local invariants sum to
zero. -/
theorem range_brLocalization : (brLocalization K).range = (sumLocalInv K).ker := by
  refine le_antisymm (fun _ ⟨x, hx⟩ ↦ hx ▸ sumLocalInv_brLocalization_eq_zero K x) fun y hy ↦ ?_
  -- The family is the localization of an idele class `z` over `G_K`, which is the class over
  -- `G_K` of a class `z'` of a layer `V ◁ G_K`.
  obtain ⟨z, rfl⟩ := ideleLocalization_surjective K y
  let L : NormalLayer (AbsoluteGaloisGroup K) := NormalLayer.ofOpenNormal
    { toOpenSubgroup := ⊤, isNormal' := inferInstanceAs (⊤ : Subgroup _).Normal }
  obtain ⟨L', -, z', hz'⟩ := exists_refinement_ideleLayerCorInfl_eq_index_nsmul K L z
  rw [NormalLayer.ground_ofOpenNormal, OpenSubgroup.toSubgroup_top, Subgroup.index_top,
    one_nsmul] at hz'
  -- Its local invariants sum to zero, so it comes from the multiplicative group of the layer.
  obtain ⟨w, rfl⟩ : z' ∈ (multiplicativeToIdeleH2 K L').range := by
    rw [← ker_ideleToClassH2, AddMonoidHom.mem_ker, ideleToClassH2_eq_zero_iff,
      ideleSumLocalInv_apply, hz', ← AddMonoidHom.mem_ker]
    exact hy
  exact ⟨_, by rw [← hz', ideleLayerCorInfl_multiplicativeToIdeleH2,
    ideleLocalization_principalIdele]⟩

/-- **Every admissible family of local invariants is that of a global Brauer class.** Let `f`
assign an element of `ℚ/ℤ` to every finite place of `K`, vanishing outside the finite set `S`,
and `g` an element of `ℚ/ℤ` to every infinite place, killed by `2` at the real places and zero at
the complex places. If all these invariants sum to zero, then they are the local invariants
`finiteInvAt` and `infiniteInvAt` of some `x ∈ Br K`. -/
theorem exists_br_of_sum_eq_zero (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : HeightOneSpectrum (𝓞 K) → AddCircle (1 : ℚ)) (hS : ∀ v ∉ S, f v = 0)
    (g : InfinitePlace K → AddCircle (1 : ℚ))
    (hgr : ∀ w : InfinitePlace K, w.IsReal → g w ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) 2)
    (hgc : ∀ w : InfinitePlace K, w.IsComplex → g w = 0)
    (hsum : ∑ v ∈ S, f v + ∑ w, g w = 0) :
    ∃ x : Br K, (∀ v : HeightOneSpectrum (𝓞 K), finiteInvAt K v x = f v) ∧
      ∀ w : InfinitePlace K, infiniteInvAt K w x = g w := by
  -- Local Brauer classes with the prescribed invariants.
  have hb (w : InfinitePlace K) : ∃ b : Br w.Completion, infiniteInvMap w b = g w := by
    rcases w.isReal_or_isComplex with hw | hw
    · rw [← Set.mem_range, range_infiniteInvMap_of_isReal w hw]
      exact hgr w hw
    · exact ⟨0, by rw [map_zero, hgc w hw]⟩
  choose b hb using hb
  have hfin : {v | (invMap (v.adicCompletion K)).symm (f v) ≠ 0}.Finite :=
    S.finite_toSet.subset fun v hv ↦ not_not.1 fun hvS ↦ hv (by rw [hS v hvS, map_zero])
  let y := (dfinsuppOfFiniteSupport _ hfin, b)
  have hy (v : HeightOneSpectrum (𝓞 K)) : invMap (v.adicCompletion K) (y.1 v) = f v := by
    rw [dfinsuppOfFiniteSupport_apply, AddEquiv.apply_symm_apply]
  -- Their invariants sum to zero, so they are the localizations of a global class.
  obtain ⟨x, hx⟩ : y ∈ (brLocalization K).range := by
    rw [range_brLocalization, AddMonoidHom.mem_ker,
      sumLocalInv_eq_sum K y fun v hv ↦ (invMap _).injective (by rw [hy, hS v hv, map_zero])]
    simpa only [hy, y, hb] using hsum
  refine ⟨x, fun v ↦ ?_, fun w ↦ ?_⟩
  · rw [finiteInvAt_apply, ← brLocalization_fst_apply, hx, hy]
  · rw [infiniteInvAt_apply, ← brLocalization_snd_apply, hx, hb]

end TauCeti.ClassFieldTheory
