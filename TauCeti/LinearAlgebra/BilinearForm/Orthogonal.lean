/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Orthogonal complements of bilinear forms

This file records facts about the orthogonal complement `LinearMap.BilinForm.orthogonal`
that Mathlib lacks. Adjoining a vector `x` whose self-pairing is a non-zero-divisor dividing all
its pairings (over a field: a non-isotropic vector) to an orthogonal basis of the orthogonal
complement of `x` gives an orthogonal basis of the whole module, for a reflexive form; this is the
inductive step of every diagonalization argument, over a field as over a valuation ring.
Over a field in which `2` is invertible, a prescribed anisotropic vector or orthogonal pair
extends to an orthogonal basis; no regularity of the ambient form is needed. Three mutually
orthogonal anisotropic vectors also supply anisotropic vectors in the intersections of
orthogonal complements used to compare bases.
Adjoining an orthogonal vector whose self-pairing is a right non-zero-divisor to a left-separating
subspace of a reflexive bilinear space produces a nondegenerate restriction; this is the
structural step used when a Cartan--Dieudonne argument enlarges a fixed subspace.

## Main results

* `LinearMap.BilinForm.iSupIndep_of_restrict_separatingRight`: pairwise orthogonal submodules on
  which the form is right-separating are independent.
* `LinearMap.BilinForm.apply_eq_zero_of_mem_biSup`: in a pairwise orthogonal family, the sums over
  disjoint sets of indices are orthogonal.
* `LinearMap.BilinForm.equivalent_of_isInternal`: orthogonal internal direct sums of isometric
  forms are isometric.
* `LinearMap.BilinForm.IsRefl.exists_orthogonal_basis_of_orthogonal_span_singleton`: an
  orthogonal basis of `x^⊥` extends by `x` to an orthogonal basis of the whole space.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_apply_zero_eq` and
  `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_apply_zero_one_eq`: extend a prescribed
  anisotropic vector or orthogonal pair to an orthogonal basis.
* `LinearMap.BilinForm.exists_apply_self_ne_zero_isOrtho_pair`: find an anisotropic vector
  orthogonal to a given vector and to one member of an anisotropic orthogonal triple.
* `TauCeti.BilinForm.restrict_nondegenerate_sup_span_singleton`: adjoining an orthogonal vector
  to a left-separating subspace produces a nondegenerate restriction.
* `LinearMap.BilinForm.isCompl_orthogonal_of_flip_restrict_bijective`: a perfect flipped
  restriction splits a bilinear module over a commutative ring.
* `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_bijective`: a perfect symmetric
  restriction splits a bilinear module over a commutative ring.
* `LinearMap.BilinForm.restrict_span_singleton_bijective_of_isUnit`: unit self-pairing makes
  the cyclic restriction perfect.
* `LinearMap.BilinForm.isCompl_span_singleton_orthogonal_of_dvd`: a vector whose self-pairing is
  a non-zero-divisor dividing all its pairings splits off.
* `LinearMap.BilinForm.isCompl_span_singleton_orthogonal_of_isUnit`: a vector with unit
  self-pairing splits off.
* `LinearMap.BilinForm.IsAlt.sup_span_singleton_le_orthogonal`: adjoining an orthogonal vector
  to an isotropic submodule preserves isotropy for an alternating form.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §1.3 (orthogonal bases).
-/

public section

namespace LinearMap.BilinForm

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- A family of pairwise orthogonal submodules, on each of which the form is right-separating, is
independent. -/
theorem iSupIndep_of_restrict_separatingRight (B : LinearMap.BilinForm K V) {ι : Type*}
    {N : ι → Submodule K V} (hO : ∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0)
    (hN : ∀ i, (B.restrict (N i)).SeparatingRight) : iSupIndep N := by
  refine fun i ↦ Submodule.disjoint_def.mpr fun x hxi hx ↦ ?_
  have hle : ⨆ (j) (_ : j ≠ i), N j ≤ B.orthogonal (N i) :=
    iSup₂_le fun j hj y hy z hz ↦ hO i j (Ne.symm hj) z hz y hy
  exact congrArg Subtype.val (hN i ⟨x, hxi⟩ fun z ↦ hle hx z z.2)

/-- In a family of pairwise orthogonal submodules, the sums of the members indexed by two disjoint
sets are orthogonal. -/
theorem apply_eq_zero_of_mem_biSup (B : LinearMap.BilinForm K V) {ι : Type*}
    {N : ι → Submodule K V} (hO : ∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0)
    {s t : Set ι} (hst : Disjoint s t) {x y : V} (hx : x ∈ ⨆ i ∈ s, N i)
    (hy : y ∈ ⨆ j ∈ t, N j) : B x y = 0 := by
  have hle : ⨆ i ∈ s, N i ≤ ⨅ y ∈ ⨆ j ∈ t, N j, LinearMap.ker (B.flip y) :=
    iSup₂_le fun i hi x hx ↦ by
      have hker : ⨆ j ∈ t, N j ≤ LinearMap.ker (B x) :=
        iSup₂_le fun j hj y hy ↦ hO i j (hst.ne_of_mem hi hj) x hx y hy
      simpa only [Submodule.mem_iInf, LinearMap.mem_ker, flip_apply] using fun y hy ↦ hker hy
  simpa using (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp (hle hx) y) hy

/-- **Orthogonal sums of isometric forms are isometric.** If two modules are internal direct sums
of pairwise orthogonal families of submodules indexed by the same type, and the restrictions of the
forms to corresponding members are isometric, then the forms are isometric. -/
theorem equivalent_of_isInternal {M : Type*} [AddCommMonoid M] [Module K M] {ι : Type*}
    [DecidableEq ι] {B : LinearMap.BilinForm K V} {B' : LinearMap.BilinForm K M}
    {N : ι → Submodule K V} {N' : ι → Submodule K M} (hN : DirectSum.IsInternal N)
    (hN' : DirectSum.IsInternal N')
    (hO : ∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0)
    (hO' : ∀ i j, i ≠ j → ∀ x ∈ N' i, ∀ y ∈ N' j, B' x y = 0)
    (h : ∀ i, (B.restrict (N i)).Equivalent (B'.restrict (N' i))) : B.Equivalent B' := by
  let u i : N i ≃ₗ[K] N' i := (h i).some.toLinearEquiv
  let e := DirectSum.congrLinearEquiv u
  -- Both forms, pulled back to `⨁ i, N i`, agree on pairs of generators.
  have key : B.compl₁₂ (DirectSum.coeLinearMap N) (DirectSum.coeLinearMap N) =
      B'.compl₁₂ (DirectSum.coeLinearMap N' ∘ₗ e.toLinearMap)
        (DirectSum.coeLinearMap N' ∘ₗ e.toLinearMap) := by
    refine DirectSum.linearMap_ext K fun i ↦ LinearMap.ext fun x ↦
      DirectSum.linearMap_ext K fun j ↦ LinearMap.ext fun y ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, e,
      DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    by_cases hij : i = j
    · subst hij
      exact ((h i).some.map_app y x).symm
    · rw [hO i j hij _ x.2 _ y.2, hO' i j hij _ (u i x).2 _ (u j y).2]
  let c := LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hN
  have hc (x : V) : DirectSum.coeLinearMap N (c.symm x) = x := c.apply_symm_apply x
  refine ⟨⟨c.symm ≪≫ₗ e ≪≫ₗ LinearEquiv.ofBijective (DirectSum.coeLinearMap N') hN',
    fun x y ↦ ?_⟩⟩
  -- The isometry decomposes `x`, applies the isometries `u i` and recombines; the first step of
  -- the calculation spells this composite out.
  calc B' (DirectSum.coeLinearMap N' (e (c.symm x))) (DirectSum.coeLinearMap N' (e (c.symm y)))
      = B (DirectSum.coeLinearMap N (c.symm x)) (DirectSum.coeLinearMap N (c.symm y)) :=
        (LinearMap.congr_fun₂ key _ _).symm
    _ = B x y := by rw [hc, hc]

end LinearMap.BilinForm

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- Adjoining a vector whose self-pairing is a right non-zero-divisor from the orthogonal complement
of a left-separating subspace preserves nondegeneracy. -/
theorem restrict_nondegenerate_sup_span_singleton
    (B : BilinForm K V) (hB : B.IsRefl) (W : Submodule K V)
    (hW : (B.restrict W).SeparatingLeft) (x : V) (hxx : B x x ∈ nonZeroDivisorsRight K)
    (hx : x ∈ B.orthogonal W) :
    (B.restrict (W ⊔ Submodule.span K {x})).Nondegenerate := by
  let S : Submodule K V := W ⊔ Submodule.span K {x}
  have hleft : (B.restrict S).SeparatingLeft := by
    intro y hy
    obtain ⟨w, hw, z, hz, hsum⟩ := Submodule.mem_sup.mp y.2
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hwzero : ∀ w' : W, B w w' = 0 := by
      intro w'
      have hBxw' : B x w' = 0 := hB.eq_zero (hx w' w'.2)
      have hyw := hy ⟨w', Submodule.mem_sup_left w'.2⟩
      -- Expose the ambient bilinear form under its restriction to `S`.
      change B y w' = 0 at hyw
      rw [← hsum] at hyw
      simpa [hBxw'] using hyw
    have hw0 : w = 0 := congrArg Subtype.val (hW ⟨w, hw⟩ hwzero)
    have hxS : x ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have hyx := hy ⟨x, hxS⟩
    -- Expose the ambient bilinear form under its restriction to `S`.
    change B y x = 0 at hyx
    rw [← hsum, hw0, zero_add] at hyx
    have ha : a = 0 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hyx
      exact hxx a (by simpa using hyx)
    apply Subtype.ext
    simp [← hsum, hw0, ha]
  refine ⟨hleft, fun y hy ↦ hleft y fun z ↦ ?_⟩
  exact (hB.domRestrict S).eq_zero (hy z)

end BilinForm

end TauCeti

namespace LinearMap.BilinForm

open Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Adjoining an orthogonal vector to an isotropic submodule preserves isotropy for an
alternating form. No nondegeneracy or characteristic assumption is needed. -/
theorem IsAlt.sup_span_singleton_le_orthogonal {B : LinearMap.BilinForm R M} (hB : B.IsAlt)
    {W : Submodule R M} (hW : W ≤ B.orthogonal W) {v : M} (hv : v ∈ B.orthogonal W) :
    W ⊔ R ∙ v ≤ B.orthogonal (W ⊔ R ∙ v) := by
  have hspan : R ∙ v ≤ B.orthogonal W := Submodule.span_le.mpr (by simpa using hv)
  rw [orthogonal, Submodule.orthogonalBilin_sup]
  refine sup_le (le_inf hW ?_) (le_inf hspan ?_)
  · intro w hw
    rw [Submodule.mem_orthogonalBilin_span]
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hB.isRefl.eq_zero ((mem_orthogonal_iff.mp hv) w hw)
  · apply Submodule.span_le.mpr
    simpa [Submodule.mem_orthogonalBilin_span] using hB v

/-- A submodule with perfect flipped restricted pairing is complementary to its right orthogonal
complement. -/
theorem isCompl_orthogonal_of_flip_restrict_bijective
    (B : LinearMap.BilinForm R M) (S : Submodule R M)
    (h : Function.Bijective (B.flip.restrict S)) :
    IsCompl S (B.orthogonal S) := by
  let e : S ≃ₗ[R] Module.Dual R S :=
    LinearEquiv.ofBijective (B.flip.restrict S) h
  let p : M →ₗ[R] S := e.symm.toLinearMap.comp (B.flip.domRestrict₂ S)
  have hp : ∀ y : S, p y = y := by
    intro y
    apply e.injective
    ext z
    simp [p, e, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict₂_apply, LinearMap.BilinForm.flip_apply]
  have hker : LinearMap.ker p = B.orthogonal S := by
    ext x
    rw [LinearMap.mem_ker, ← e.map_eq_zero_iff]
    have hpx : e (p x) = B.flip.domRestrict₂ S x := by simp [p]
    rw [hpx]
    constructor
    · intro hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      have hy' := congrArg (fun f : Module.Dual R S ↦ f ⟨y, hy⟩) hx
      simpa [LinearMap.domRestrict₂_apply, LinearMap.BilinForm.flip_apply] using hy'
    · intro hx
      ext y
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y y.property
  rw [← hker]
  exact LinearMap.isCompl_of_proj hp

/-- A submodule with perfect symmetric restricted pairing is complementary to its orthogonal
complement. -/
theorem isCompl_orthogonal_of_restrict_bijective
    (B : LinearMap.BilinForm R M) (S : Submodule R M) (hB : (B.restrict S).IsSymm)
    (h : Function.Bijective (B.restrict S)) :
    IsCompl S (B.orthogonal S) := by
  have hflip : B.flip.restrict S = B.restrict S := by
    ext x y
    simpa [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.flip_apply] using
      (hB.eq y x)
  exact B.isCompl_orthogonal_of_flip_restrict_bijective S (hflip ▸ h)

/-- Unit self-pairing makes the restricted pairing on the cyclic span perfect. -/
theorem restrict_span_singleton_bijective_of_isUnit (B : LinearMap.BilinForm R M)
    (x : M) (hx : IsUnit (B x x)) : Function.Bijective (B.restrict (R ∙ x)) := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hx
  have ha' : a * B x x = 1 := by simpa [mul_comm] using ha
  let S : Submodule R M := R ∙ x
  have hxS : x ∈ S := Submodule.mem_span_singleton_self x
  constructor
  · intro y z hyz
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp z.property
    have hval : B (y : M) x = B (z : M) x := by
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using
        congrArg (fun f : Module.Dual R S ↦ f ⟨x, hxS⟩) hyz
    rw [← hb, ← hc, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at hval
    simp only [smul_eq_mul] at hval
    have hbc : b = c := by
      calc
        b = (a * B x x) * b := by rw [ha']; ring
        _ = a * (b * B x x) := by ring
        _ = a * (c * B x x) := by rw [hval]
        _ = c := by calc
          a * (c * B x x) = c * (a * B x x) := by ring
          _ = c := by rw [ha', mul_one]
    apply Subtype.ext
    rw [← hb, ← hc, hbc]
  · intro f
    refine ⟨⟨(a * f ⟨x, hxS⟩) • x, Submodule.smul_mem S _ hxS⟩, ?_⟩
    ext y
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    have hy : y = b • (⟨x, hxS⟩ : S) := Subtype.ext hb.symm
    rw [hy]
    simp only [LinearMap.BilinForm.restrict_apply]
    rw [map_smul, map_smul, map_smul]
    simp only [smul_eq_mul]
    calc
      b * (a * f ⟨x, hxS⟩ * B x x) = b * (a * B x x) * f ⟨x, hxS⟩ := by ring
      _ = b * f ⟨x, hxS⟩ := by rw [ha']; ring

/-- A vector `x` whose self-pairing `B x x` is a non-zero-divisor dividing every pairing `B x y`
spans an orthogonal direct summand. Over a field this is the condition `B x x ≠ 0`; over a
valuation ring it says that `B x x` has minimal valuation among the pairings of `x`. -/
theorem isCompl_span_singleton_orthogonal_of_dvd (B : LinearMap.BilinForm R M) {x : M}
    (hx : B x x ∈ nonZeroDivisors R) (hdvd : ∀ y, B x x ∣ B x y) :
    IsCompl (R ∙ x) (B.orthogonal (R ∙ x)) := by
  refine ⟨Submodule.disjoint_def.mpr fun y hy hy' ↦ ?_, codisjoint_iff.mpr ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc := (mem_orthogonal_iff.mp hy') x (Submodule.mem_span_singleton_self x)
    rw [map_smul, smul_eq_mul] at hc
    rw [(mem_nonZeroDivisors_iff_right.mp hx) c hc, zero_smul]
  · refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨k, hk⟩ := hdvd z
    refine Submodule.mem_sup.mpr ⟨k • x, Submodule.smul_mem _ k
      (Submodule.mem_span_singleton_self x), z - k • x, mem_orthogonal_iff.mpr fun n hn ↦ ?_,
      add_sub_cancel _ _⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
    simp only [map_smul, map_sub, LinearMap.smul_apply, smul_eq_mul, hk]
    ring

/-- Adjoining a vector `x` to an orthogonal basis of the orthogonal complement of `x` gives an
orthogonal basis of the whole module, for a reflexive form, provided the self-pairing `B x x` is a
non-zero-divisor dividing every pairing `B x y`. Over a field this says `B x x ≠ 0`.
The resulting basis starts with `x`, followed by the supplied basis of its complement. -/
theorem IsRefl.exists_orthogonal_basis_of_orthogonal_span_singleton {B : LinearMap.BilinForm R M}
    (hB : B.IsRefl) {x : M} (hx : B x x ∈ nonZeroDivisors R) (hdvd : ∀ y, B x x ∣ B x y)
    {d : ℕ} {v : Basis (Fin d) R (B.orthogonal (R ∙ x))}
    (hv : (B.restrict (B.orthogonal (R ∙ x))).iIsOrtho v) :
    ∃ b : Basis (Fin (d + 1)) R M, B.iIsOrtho b ∧
      b 0 = x ∧ ∀ i, b i.succ = (v i : M) := by
  have hc := B.isCompl_span_singleton_orthogonal_of_dvd hx hdvd
  have hli : ∀ c : R, ∀ y ∈ B.orthogonal (R ∙ x), c • x + y = 0 → c = 0 := fun c y hy hcy ↦ by
    have hcx : c • x ∈ B.orthogonal (R ∙ x) := by
      rw [eq_neg_of_add_eq_zero_left hcy]
      exact neg_mem hy
    have hzero : c • x = 0 :=
      Submodule.disjoint_def.mp hc.disjoint (c • x) (Submodule.smul_mem _ c
        (Submodule.mem_span_singleton_self x)) hcx
    have h := congrArg (B x) hzero
    rw [map_smul, smul_eq_mul, map_zero] at h
    exact mem_nonZeroDivisors_iff_right.mp hx c h
  have hsp : ∀ z : M, ∃ c : R, z + c • x ∈ B.orthogonal (R ∙ x) := fun z ↦ by
    obtain ⟨w, hw, y, hy, hwy⟩ := Submodule.mem_sup.mp
      (hc.sup_eq_top ▸ (Submodule.mem_top : z ∈ (⊤ : Submodule R M)))
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨-k, by simpa [← hwy, add_comm, add_left_comm, add_assoc] using hy⟩
  refine ⟨Basis.mkFinCons x v hli hsp, ?_, ?_, ?_⟩
  rotate_left
  · simp [Basis.coe_mkFinCons]
  · intro i
    simp [Basis.coe_mkFinCons]
  rw [iIsOrtho_def, Basis.coe_mkFinCons]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · simpa [orthogonal] using (v j).2
  · exact hB.eq_zero (by simpa [orthogonal] using (v i).2)
  · simpa using iIsOrtho_def.1 hv i j fun h => hij (congrArg Fin.succ h)

/-- A vector with unit self-pairing spans an orthogonal direct summand. -/
theorem isCompl_span_singleton_orthogonal_of_isUnit
    (B : LinearMap.BilinForm R M) (x : M) (hx : IsUnit (B x x)) :
    IsCompl (R ∙ x) (B.orthogonal (R ∙ x)) :=
  B.isCompl_span_singleton_orthogonal_of_dvd hx.mem_nonZeroDivisors fun _ ↦ hx.dvd

end LinearMap.BilinForm

namespace LinearMap.BilinForm

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : LinearMap.BilinForm K V}

/-- The orthogonal complement of a vector with nonzero self-pairing has codimension one,
without any symmetry or characteristic assumption on the bilinear form. -/
theorem finrank_orthogonal_span_singleton_add_one (B : LinearMap.BilinForm K V) {x : V}
    (hx : B x x ≠ 0) : finrank K (B.orthogonal (K ∙ x)) + 1 = finrank K V := by
  simpa only [finrank_span_singleton (ne_zero_of_not_isOrtho_self x hx), add_comm] using
    Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)

variable [Invertible (2 : K)]

/-- A vector with nonzero self-pairing extends to an orthogonal basis of a symmetric bilinear
space, with that vector in the first position. -/
theorem IsSymm.exists_orthogonal_basis_apply_zero_eq (hB : B.IsSymm) {x : V}
    (hx : B x x ≠ 0) {n : ℕ} (hdim : finrank K V = n + 1) :
    ∃ b : Basis (Fin (n + 1)) K V, B.IsOrthoᵢ b ∧ b 0 = x := by
  have hN : finrank K (B.orthogonal (K ∙ x)) = n := by
    have h := B.finrank_orthogonal_span_singleton_add_one hx
    omega
  obtain ⟨v, hv⟩ := exists_orthogonal_basis (isSymm_iff.mp (hB.restrict (B.orthogonal (K ∙ x))))
  let v' := v.reindex (finCongr hN)
  have hv' : (B.restrict (B.orthogonal (K ∙ x))).IsOrthoᵢ v' := by
    intro i j hij
    simpa only [Function.onFun, v', Basis.reindex_apply] using
      hv ((finCongr hN).symm.injective.ne hij)
  obtain ⟨b, hb, hzero, -⟩ := hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton
    (mem_nonZeroDivisors_of_ne_zero hx) (fun _ ↦ hx.isUnit.dvd) hv'
  exact ⟨b, hb, hzero⟩

/-- An orthogonal pair with nonzero self-pairings extends to an orthogonal basis of a symmetric
bilinear space, with the pair in the first two positions. -/
theorem IsSymm.exists_orthogonal_basis_apply_zero_one_eq (hB : B.IsSymm) {x y : V}
    (hx : B x x ≠ 0) (hy : B y y ≠ 0) (hxy : B x y = 0) {n : ℕ}
    (hdim : finrank K V = n + 2) :
    ∃ b : Basis (Fin (n + 2)) K V, B.IsOrthoᵢ b ∧ b 0 = x ∧ b 1 = y := by
  let N := B.orthogonal (K ∙ x)
  let y' : N := ⟨y, by simpa [N, orthogonal] using hxy⟩
  have hN : finrank K N = n + 1 := by
    have h := B.finrank_orthogonal_span_singleton_add_one hx
    dsimp only [N]
    omega
  obtain ⟨v, hv, hvzero⟩ := (hB.restrict N).exists_orthogonal_basis_apply_zero_eq
    (x := y') hy hN
  obtain ⟨b, hb, hbzero, hbsucc⟩ := hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton
    (mem_nonZeroDivisors_of_ne_zero hx) (fun _ ↦ hx.isUnit.dvd) hv
  exact ⟨b, hb, hbzero, (hbsucc 0).trans (congrArg Subtype.val hvzero)⟩

end LinearMap.BilinForm

namespace LinearMap.BilinForm

variable {K V : Type*} [CommRing K] [IsDomain K] [NeZero (2 : K)]
  [AddCommGroup V] [Module K V]

/-- Given three mutually orthogonal vectors with nonzero self-pairings, every vector is
orthogonal to a vector with nonzero self-pairing which is also orthogonal to one of the three.
This supplies the shared vector in comparisons of orthogonal bases in dimension at least three. -/
theorem exists_apply_self_ne_zero_isOrtho_pair (B : LinearMap.BilinForm K V)
    (v : Fin 3 → V) (hv : B.IsOrthoᵢ v) (hvv : ∀ i, B (v i) (v i) ≠ 0) (u : V) :
    ∃ z : V, B z z ≠ 0 ∧ B u z = 0 ∧ ∃ k : Fin 3, B (v k) z = 0 := by
  let a : Fin 3 → K := fun i ↦ B (v i) (v i)
  let c : Fin 3 → K := fun i ↦ B u (v i)
  have pair (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
      (h : a i * c j ^ 2 + a j * c i ^ 2 ≠ 0) :
      ∃ z : V, B z z ≠ 0 ∧ B u z = 0 ∧ ∃ k : Fin 3, B (v k) z = 0 := by
    refine ⟨c j • v i - c i • v j, ?_, ?_, k, ?_⟩
    · have heq : B (c j • v i - c i • v j) (c j • v i - c i • v j) =
          a i * c j ^ 2 + a j * c i ^ 2 := by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hv hij, hv hij.symm, a]
        ring
      exact heq ▸ h
    · simp only [map_sub, map_smul, smul_eq_mul, c]
      ring
    · simp [hv hki, hv hkj]
  by_cases h01 : a 0 * c 1 ^ 2 + a 1 * c 0 ^ 2 ≠ 0
  · exact pair 0 1 2 (by decide) (by decide) (by decide) h01
  by_cases h02 : a 0 * c 2 ^ 2 + a 2 * c 0 ^ 2 ≠ 0
  · exact pair 0 2 1 (by decide) (by decide) (by decide) h02
  by_cases h12 : a 1 * c 2 ^ 2 + a 2 * c 1 ^ 2 ≠ 0
  · exact pair 1 2 0 (by decide) (by decide) (by decide) h12
  -- If all three binary combinations are isotropic, their equations force all three pairings
  -- with `u` to vanish. The factor `2` is the reason characteristic two is excluded.
  have heq01 := not_ne_iff.mp h01
  have heq02 := not_ne_iff.mp h02
  have heq12 := not_ne_iff.mp h12
  have hzero : 2 * a 1 * a 2 * c 0 ^ 2 = 0 := by
    linear_combination a 2 * heq01 + a 1 * heq02 - a 0 * heq12
  have hc0 : c 0 = 0 := by
    have hcoeff : 2 * a 1 * a 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (two_ne_zero' K) (hvv 1)) (hvv 2)
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hzero).resolve_left hcoeff)
  have hc1 : c 1 = 0 := by
    rw [hc0, zero_pow two_ne_zero, mul_zero, add_zero] at heq01
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp heq01).resolve_left (hvv 0))
  exact ⟨v 1, hvv 1, hc1, 0, hv (by decide : (0 : Fin 3) ≠ 1)⟩

end LinearMap.BilinForm
