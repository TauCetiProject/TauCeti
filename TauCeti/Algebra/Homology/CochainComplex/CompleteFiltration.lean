/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration

import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.CategoryTheory.Subobject.Cokernel

/-!
# Acyclicity along complete filtrations of cochain complexes

Let `G 0 ⊇ G 1 ⊇ ⋯` be subcomplexes of a cochain complex of modules `K`. The key statement is
`CochainComplex.isZero_homology_of_isCompleteFiltration`: if, degreewise, the chain is complete and
separated (Tau Ceti's `TauCeti.IsCompleteFiltration`) in degree `m - 1` and separated in degree
`m`, and the quotients `G k / G (k + 1)` have vanishing `H^m`, then the first term `G 0` has
vanishing `H^m`. A cocycle `z` in `G 0` is pushed down the chain one stage at a time
(`CochainComplex.exists_sub_d_mem_range_of_isZero_homology_cokernel`), `z = d y₀ + ⋯ + d y_{k-1}
+ z_k` with `y_i ∈ G i` and `z_k ∈ G k`; completeness in degree `m - 1` sums the series `∑ yᵢ`,
and separation in degree `m` shows that its coboundary is `z`. This is the elementwise form of
the Mittag-Leffler argument through the Milnor sequence of the tower `G 0 / G k`: the vanishing
of `H^m` on the graded pieces gives surjective transitions on `H^{m-1}` of that tower, hence no
`lim¹` term. Only `H^m` of the graded pieces enters.

For an increasing filtration indexed by `ℤ` this gives the acyclicity of `F_a` from that of the
graded pieces below `a` (`CochainComplex.isZero_homology_of_isCompleteFiltration_of_monotone`),
and dually for decreasing filtrations above `p`
(`CochainComplex.isZero_homology_of_isCompleteFiltration_of_antitone`). These are the inputs to
the convergence theorems of `TauCeti.Algebra.Homology.SpectralSequence.Filtered.Complete`.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.10.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

universe v

variable {R : Type*} [Ring R] {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- **Pushing a cocycle down one stage.** Let `S ≤ T` be subcomplexes of `K` such that `T/S` has
vanishing `H^m`. Then every cocycle `z ∈ K^m` lying in `T` differs from a cocycle lying in `S` by
the coboundary `d y` of some `y ∈ T^{m-1}`. -/
lemma exists_sub_d_mem_range_of_isZero_homology_cokernel {S T : Subobject K} (hST : S ≤ T)
    {m' m : ℤ} (hm : m' + 1 = m)
    (h : IsZero ((cokernel (Subobject.ofLE S T hST)).homology m)) {z : K.X m}
    (hz : z ∈ LinearMap.range (T.arrow.f m).hom) (hdz : (K.d m (m + 1)).hom z = 0) :
    ∃ y ∈ LinearMap.range (T.arrow.f m').hom,
      z - (K.d m' m).hom y ∈ LinearMap.range (S.arrow.f m).hom := by
  obtain ⟨z, rfl⟩ := hz
  have hinj (U : Subobject K) (n : ℤ) : Function.Injective (U.arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hdz' : ((T : CochainComplex (ModuleCat R) ℤ).d m (m + 1)).hom z = 0 :=
    hinj T _ (by rw [← HomologicalComplex.Hom.comm_apply, hdz, map_zero])
  -- The image of `z` in `T/S` is a cocycle, homologous to zero since `H^m(T/S) = 0`.
  let S' := ShortComplex.cokernelSequence (Subobject.ofLE S T hST)
  have hdz₃ : (S'.X₃.d m (m + 1)).hom ((S'.g.f m).hom z) = 0 :=
    HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero S'.g m (m + 1) z hdz'
  -- The terms `S'.X₁` and `S'.X₂` are `S` and `T` by definition (`cokernelSequence_X₁`,
  -- `cokernelSequence_X₂`); the type ascriptions below record the elements in these terms.
  obtain ⟨b, a, hab⟩ : ∃ (b : (T : CochainComplex (ModuleCat R) ℤ).X m')
      (a : (S : CochainComplex (ModuleCat R) ℤ).X m),
      z = ((T : CochainComplex (ModuleCat R) ℤ).d m' m).hom b +
        ((Subobject.ofLE S T hST).f m).hom a := by
    obtain ⟨b, a, -, hab⟩ := (TauCeti.cokernelSequence_shortExact
      (Subobject.ofLE S T hST)).moduleCat_exists_sub_eq_d_add m (m + 1) m' (by simp; lia) z 0
      (by exact hdz'.trans (map_zero _).symm)
      (S'.X₃.moduleCatCyclesMk _ (m + 1) (by simp) hdz₃) 0
      (by exact (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm) (by simp)
      ((ModuleCat.isZero_iff_subsingleton.1 h).elim _ _)
    exact ⟨b, a, (sub_zero z).symm.trans hab⟩
  -- So `z = d b + a` with `b ∈ T^{m-1}` and `a ∈ S^m`.
  refine ⟨_, ⟨b, rfl⟩, a, ?_⟩
  rw [HomologicalComplex.Hom.comm_apply, ← map_sub, hab, add_sub_cancel_left,
    ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.comp_f]
  exact congr(($(Subobject.ofLE_arrow hST).f m).hom a).symm

/-- **Acyclicity of the first term of a complete chain of subcomplexes.** Let
`G 0 ⊇ G 1 ⊇ G 2 ⊇ ⋯` be subcomplexes of a complex of modules `K` which, degreewise, form a
complete separated filtration in degree `m - 1` and a separated one in degree `m`. If every
quotient `G k / G (k + 1)` has vanishing `H^m`, then so does `G 0`. -/
theorem isZero_homology_of_isCompleteFiltration (G : ℕ → Subobject K) (hG : Antitone G)
    {m' m : ℤ} (hm : m' + 1 = m)
    (hc₀ : TauCeti.IsCompleteFiltration fun k ↦ LinearMap.range ((G k).arrow.f m').hom)
    (hsep : ∀ z, (∀ k, z ∈ LinearMap.range ((G k).arrow.f m).hom) → z = 0)
    (h : ∀ k : ℕ,
      IsZero ((cokernel (Subobject.ofLE (G (k + 1)) (G k) (hG k.le_succ))).homology m)) :
    IsZero ((G 0 : CochainComplex (ModuleCat R) ℤ).homology m) := by
  -- Every cocycle of `K` in `G k` is cohomologous, within `G k`, to a cocycle in `G (k + 1)`.
  have step (k : ℕ) (z : K.X m) (hz : z ∈ LinearMap.range ((G k).arrow.f m).hom)
      (hdz : (K.d m (m + 1)).hom z = 0) :
      ∃ y ∈ LinearMap.range ((G k).arrow.f m').hom,
        z - (K.d m' m).hom y ∈ LinearMap.range ((G (k + 1)).arrow.f m).hom :=
    exists_sub_d_mem_range_of_isZero_homology_cokernel (hG k.le_succ) hm (h k) hz hdz
  choose! y hy hyz using step
  -- Iterating, a cocycle `z` in `G 0` gives cocycles `zs k ∈ G k` with
  -- `zs k = z - d (y 0 + ⋯ + y (k - 1))`, and the series `∑ y k` converges.
  have key (z : K.X m) (hz : z ∈ LinearMap.range ((G 0).arrow.f m).hom)
      (hdz : (K.d m (m + 1)).hom z = 0) :
      ∃ s ∈ LinearMap.range ((G 0).arrow.f m').hom, (K.d m' m).hom s = z := by
    let zs : ℕ → K.X m := fun k ↦ Nat.rec z (fun k zk ↦ zk - (K.d m' m).hom (y k zk)) k
    have hzs_succ (k : ℕ) : zs (k + 1) = zs k - (K.d m' m).hom (y k (zs k)) := rfl
    have hzs (k : ℕ) :
        zs k ∈ LinearMap.range ((G k).arrow.f m).hom ∧ (K.d m (m + 1)).hom (zs k) = 0 := by
      induction k with
      | zero => exact ⟨hz, hdz⟩
      | succ k ih =>
        rw [hzs_succ]
        refine ⟨hyz k _ ih.1 ih.2, ?_⟩
        rw [map_sub, ih.2, HomologicalComplex.d_comp_d_apply, sub_zero]
    have hzsum (n : ℕ) : zs n = z - (K.d m' m).hom (∑ k ∈ Finset.range n, y k (zs k)) := by
      induction n with
      | zero => simp [zs]
      | succ n ih =>
        rw [hzs_succ, Finset.sum_range_succ, map_add, ← sub_sub, ← ih]
    obtain ⟨s, hs⟩ := hc₀.exists_limit (fun n ↦ ∑ k ∈ Finset.range n, y k (zs k)) fun n ↦ by
      simpa [Finset.sum_range_succ] using hy n _ (hzs n).1 (hzs n).2
    refine ⟨s, by simpa using hs 0, sub_eq_zero.1 (hsep _ fun n ↦ ?_)⟩
    have hsub : (K.d m' m).hom s - z =
        (K.d m' m).hom (s - ∑ k ∈ Finset.range n, y k (zs k)) - zs n := by
      rw [hzsum n, map_sub]
      abel
    rw [hsub]
    obtain ⟨t, ht⟩ := hs n
    exact sub_mem ⟨_, by rw [← ht, HomologicalComplex.Hom.comm_apply]⟩ (hzs n).1
  -- Transport the statement from `K` to the subcomplex `G 0`.
  have hinj (n : ℤ) : Function.Injective ((G 0).arrow.f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((HomologicalComplex.exactAt_iff' _ m' m (m + 1) (by simp; lia) (by simp)).2
      ((ShortComplex.moduleCat_exact_iff _).2 fun x hx ↦ ?_))
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := key _ ⟨x, rfl⟩
    (HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero (G 0).arrow m (m + 1) x hx)
  exact ⟨s, hinj m ((HomologicalComplex.Hom.comm_apply (G 0).arrow m' m s).symm.trans hs)⟩

/-- **Acyclicity of a stage of a complete increasing filtration.** Let `F` be an increasing
filtration of a complex of modules `K` which, degreewise, is complete and separated below `F_a` in
degree `m - 1` and separated below `F_a` in degree `m`. If the graded pieces `F_{i+1}/F_i` have
vanishing `H^m` for all `i < a`, then so does `F_a`. -/
theorem isZero_homology_of_isCompleteFiltration_of_monotone (F : ℤ → Subobject K)
    (hF : Monotone F) {a m' m : ℤ} (hm : m' + 1 = m)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (a - k)).arrow.f m').hom)
    (hsep : ∀ z, (∀ k : ℕ, z ∈ LinearMap.range ((F (a - k)).arrow.f m).hom) → z = 0)
    (h : ∀ i, i < a →
      IsZero ((cokernel (Subobject.ofLE (F i) (F (i + 1)) (hF (Int.le_add_one le_rfl)))).homology
        m)) :
    IsZero ((F a : CochainComplex (ModuleCat R) ℤ).homology m) := by
  have := isZero_homology_of_isCompleteFiltration (fun k : ℕ ↦ F (a - k))
    (fun k l hkl ↦ hF (by lia)) hm hc₀ hsep fun k ↦
      (h (a - (k + 1 : ℕ)) (by lia)).of_iso ((HomologicalComplex.homologyFunctor _ _ m).mapIso
        (Subobject.cokernelOfLEIsoOfEq rfl (by congr 1; lia) _ _))
  rwa [Nat.cast_zero, sub_zero] at this

/-- **Acyclicity of a stage of a complete decreasing filtration.** Let `F` be a decreasing
filtration of a complex of modules `K` which, degreewise, is complete and separated above `F^p` in
degree `m - 1` and separated above `F^p` in degree `m`. If the graded pieces `F^j/F^{j+1}` have
vanishing `H^m` for all `j ≥ p`, then so does `F^p`. -/
theorem isZero_homology_of_isCompleteFiltration_of_antitone (F : ℤ → Subobject K)
    (hF : Antitone F) {p m' m : ℤ} (hm : m' + 1 = m)
    (hc₀ : TauCeti.IsCompleteFiltration fun k : ℕ ↦ LinearMap.range ((F (p + k)).arrow.f m').hom)
    (hsep : ∀ z, (∀ k : ℕ, z ∈ LinearMap.range ((F (p + k)).arrow.f m).hom) → z = 0)
    (h : ∀ j, p ≤ j →
      IsZero ((cokernel (Subobject.ofLE (F (j + 1)) (F j) (hF (by lia)))).homology m)) :
    IsZero ((F p : CochainComplex (ModuleCat R) ℤ).homology m) := by
  have := isZero_homology_of_isCompleteFiltration (fun k : ℕ ↦ F (p + k))
    (fun k l hkl ↦ hF (by lia)) hm hc₀ hsep fun k ↦
      (h (p + k) (by lia)).of_iso ((HomologicalComplex.homologyFunctor _ _ m).mapIso
        (Subobject.cokernelOfLEIsoOfEq (by congr 1; lia) rfl _ _))
  rwa [Nat.cast_zero, add_zero] at this

end CochainComplex
