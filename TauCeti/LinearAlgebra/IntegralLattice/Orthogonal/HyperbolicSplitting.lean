/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.SignedUnitLattice
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.UnitNorm

/-!
# Hyperbolic splitting, parity-preserving unit-norm splitting, and the even-to-odd reduction

An integral lattice `L` is rationally isotropic (`¬ L.norm.Anisotropic`) if and only if its carrier
contains a primitive isotropic vector `v`. When `L` is unimodular, surjectivity of the integral
pairing supplies a partner `u ∈ L` with `L.integralForm v u = 1`, and the rank-two sublattice
`ℤ ∙ v ⊔ ℤ ∙ u` always has bijective restricted pairing and splits off orthogonally:

* **Even hyperbolic splitting**: if `L` is even, unimodular, and rationally isotropic, modifying `u`
  by a multiple of `v` makes `u` isotropic as well, splitting off a copy of `hyperbolicPlane` with
  an even unimodular complement.
* **Odd parity-preserving unit-norm splitting**: if `L` is odd, unimodular, and rationally
  isotropic, `u` can be adjusted by an odd-norm vector in `(ℤ ∙ v ⊔ ℤ ∙ u)^⊥` so that `u` has odd
  norm `2m + 1`. Then `x₊ = u - m • v` and `x₋ = u - (m + 1) • v` are mutually orthogonal vectors
  of norms `+1` and `-1`, so splitting off `⟨1⟩` leaves `x₋` in the orthogonal complement (making
  the complement odd and unimodular) and splitting off `⟨-1⟩` leaves `x₊` in the orthogonal
  complement (likewise odd and unimodular).
* **Unconditional rank-two indefinite classification**: every unimodular lattice of signature
  `(1, 0, 1)` has Gram determinant `-1` and is therefore automatically isotropic, so it is
  isometric to `hyperbolicPlane` when even and to `indefiniteUnitPlane` (hence `I_{1, 1}`) when odd.
* **Even-to-odd reduction for indefinite unimodular classification**: splitting off a hyperbolic
  plane `L ≅ Y ⊕ hyperbolicPlane` identifies `L` with an even Kneser two-neighbor of the odd
  unimodular lattice `Y ⊕ indefiniteUnitPlane` of the same signature `(r, 0, s)`. By uniqueness of
  even two-neighbors of `I_{r, s}` (`SignedUnitLattice`), classification of odd unimodular lattices
  at signature `(r, 0, s)` implies `8 ∣ (r : ℤ) - s` and uniqueness up to isometry of rationally
  isotropic even unimodular lattices of signature `(r, 0, s)`.

## Main definitions

* `TauCeti.IntegralLattice.restrictSubmodule`: the rationalized integral lattice attached to a
  submodule `S : Submodule ℤ L`.

## Main results

* `TauCeti.IntegralLattice.not_anisotropic_norm_iff_exists_isPrimitive`: `¬ L.norm.Anisotropic` iff
  `L` has a primitive carrier vector of integral norm zero.
* `TauCeti.IntegralLattice.exists_isometry_hyperbolicPlane_orthogonalSum`: every rationally
  isotropic even unimodular lattice splits off `hyperbolicPlane` with an even unimodular complement.
* `TauCeti.IntegralLattice.exists_odd_isUnimodular_rankOne_one_orthogonalSum` and
  `TauCeti.IntegralLattice.exists_odd_isUnimodular_rankOne_neg_one_orthogonalSum`: parity-preserving
  `⟨±1⟩` orthogonal splittings for rationally isotropic odd unimodular lattices.
* `TauCeti.IntegralLattice.nonempty_isometry_hyperbolicPlane_of_isUnimodular_of_signature_one_one`
  and `nonempty_isometry_indefiniteUnitPlane_of_isUnimodular_of_signature_one_one`:
  unconditional classification of unimodular lattices of signature `(1, 0, 1)`.
* `TauCeti.IntegralLattice.exists_odd_isUnimodular_isNeighbor`: every rationally isotropic even
  unimodular lattice is isometric to an explicit even Kneser two-neighbor of an odd unimodular
  lattice of the same signature.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §§2–5.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

/-! ## Orthogonal-sum unimodularity and sublattice rationalization -/

section General

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- An orthogonal direct sum is unimodular if and only if both summands are unimodular. -/
theorem isUnimodular_orthogonalSum_iff (A : IntegralLattice V) (B : IntegralLattice W) :
    (A.orthogonalSum B).IsUnimodular ↔ A.IsUnimodular ∧ B.IsUnimodular := by
  rw [isUnimodular_iff_discriminant_eq_one, isUnimodular_iff_discriminant_eq_one,
    isUnimodular_iff_discriminant_eq_one, discriminant_orthogonalSum, mul_eq_one]

/-- The integral lattice on `ℚ ⊗[ℤ] S` obtained by rationalizing the restriction of `L.integralForm`
to a carrier submodule `S : Submodule ℤ L`. -/
noncomputable abbrev restrictSubmodule (L : IntegralLattice V) (S : Submodule ℤ L) :
    IntegralLattice (ℚ ⊗[ℤ] S) :=
  ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)

end General

/-! ## Rational isotropy and primitive isotropic vectors -/

section Isotropic

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Every ambient rational vector has a positive integer multiple lying in the lattice carrier. -/
theorem exists_pos_nsmul_mem_carrier (L : IntegralLattice V) (x : V) :
    ∃ n : ℕ, 0 < n ∧ n • x ∈ L.carrier := by
  classical
  let c := L.rationalBasis.repr x
  let D : ℕ := ∏ i ∈ c.support, (c i).den
  refine ⟨D, Finset.prod_pos fun i _ ↦ (c i).den_pos, ?_⟩
  have hx : x = ∑ i ∈ c.support, c i • L.rationalBasis i := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
      (L.rationalBasis.linearCombination_repr x).symm
  rw [hx, Finset.smul_sum]
  refine L.carrier.sum_mem fun i hi ↦ ?_
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j ↦ (c j).den) hi
  have hD : D = (c i).den * m := hm
  have hq : (D : ℚ) * c i = (((c i).num * m : ℤ) : ℚ) := by
    calc
      (D : ℚ) * c i = (m : ℚ) * (c i * (c i).den) := by rw [hD]; push_cast; ring
      _ = (((c i).num * m : ℤ) : ℚ) := by rw [Rat.mul_den_eq_num]; push_cast; ring
  rw [L.rationalBasis_apply, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hq, Int.cast_smul_eq_zsmul ℚ]
  exact L.carrier.smul_mem ((c i).num * m) (Module.Free.chooseBasis ℤ L i).2

/-- **Rational isotropy ↔ primitive carrier isotropic vector.** An integral lattice has isotropic
rational norm form (`¬ L.norm.Anisotropic`) if and only if its carrier contains a primitive vector
of integral norm zero. -/
theorem not_anisotropic_norm_iff_exists_isPrimitive (L : IntegralLattice V) :
    ¬ L.norm.Anisotropic ↔ ∃ v : L, IsPrimitive v ∧ L.integralNorm v = 0 := by
  rw [QuadraticMap.not_anisotropic_iff_exists]
  constructor
  · rintro ⟨x, hx0, hxn⟩
    obtain ⟨n, hn, hnx⟩ := L.exists_pos_nsmul_mem_carrier x
    let y : L := ⟨n • x, hnx⟩
    have hy0 : y ≠ 0 := by
      intro hy
      have hnx0 : n • x = 0 := congrArg Subtype.val hy
      rw [← Nat.cast_smul_eq_nsmul ℚ] at hnx0
      exact hx0 ((smul_eq_zero.mp hnx0).resolve_left (Nat.cast_ne_zero.mpr hn.ne'))
    have hyn : L.integralNorm y = 0 := by
      apply Int.cast_injective (α := ℚ)
      rw [L.integralNorm_cast, Int.cast_zero]
      dsimp only [y]
      rw [← Nat.cast_smul_eq_nsmul ℚ, QuadraticMap.map_smul, hxn, smul_zero]
    obtain ⟨d, v, hd, hv, hyv⟩ := exists_eq_zsmul_isPrimitive hy0
    refine ⟨v, hv, ?_⟩
    rw [hyv, QuadraticMap.map_smul, smul_eq_mul] at hyn
    exact (mul_eq_zero.mp hyn).resolve_left (mul_ne_zero hd.ne' hd.ne')
  · rintro ⟨v, hv, hvn⟩
    refine ⟨v, fun hv0 ↦ hv.ne_zero (Subtype.ext hv0), ?_⟩
    rw [← L.integralNorm_cast, hvn, Int.cast_zero]

/-- In a rationally isotropic unimodular lattice, there exist carrier vectors `v` and `u` with
`L.integralNorm v = 0` and `L.integralForm v u = 1`. -/
theorem exists_integralNorm_eq_zero_integralForm_eq_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hiso : ¬ L.norm.Anisotropic) :
    ∃ v u : L, L.integralNorm v = 0 ∧ L.integralForm v u = 1 := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  obtain ⟨v, hv, hvn⟩ := (L.not_anisotropic_norm_iff_exists_isPrimitive).mp hiso
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hv
  let u : L := (L.integralPairingEquiv hLu).symm f
  have huv : L.integralForm u v = 1 := by
    have h : (L.integralPairingEquiv hLu).toLinearMap u = f :=
      (L.integralPairingEquiv hLu).apply_symm_apply f
    rw [L.integralPairingEquiv_toLinearMap] at h
    exact (LinearMap.congr_fun h v).trans hf
  exact ⟨v, u, hvn, (L.isSymm_integralForm.eq v u).trans huv⟩

/-! ## Bijective pairing on `ℤ ∙ v ⊔ ℤ ∙ u` and hyperbolic plane splitting -/

private def isotropicPairSpan (L : IntegralLattice V) (v u : L) : Submodule ℤ L :=
  ℤ ∙ v ⊔ ℤ ∙ u

private theorem mem_isotropicPairSpan_of_zsmul (L : IntegralLattice V) (v u : L) (c₀ c₁ : ℤ) :
    c₀ • v + c₁ • u ∈ isotropicPairSpan L v u :=
  Submodule.add_mem_sup (Submodule.mem_span_singleton.mpr ⟨c₀, rfl⟩)
    (Submodule.mem_span_singleton.mpr ⟨c₁, rfl⟩)

private noncomputable def isotropicPairSpanEquiv {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hvu : L.integralForm v u = 1) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] isotropicPairSpan L v u where
  toFun c := ⟨c 0 • v + c 1 • u, mem_isotropicPairSpan_of_zsmul L v u (c 0) (c 1)⟩
  invFun p := ![L.integralForm p.1 u - L.integralNorm u * L.integralForm p.1 v,
    L.integralForm p.1 v]
  map_add' c d := by
    apply Subtype.ext
    simp only [Pi.add_apply, add_smul, Submodule.coe_add]
    abel
  map_smul' r c := by
    apply Subtype.ext
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Submodule.coe_smul, smul_add, mul_smul]
  left_inv c := by
    have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
    have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
    rw [funext_iff, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, hvv, hvu, huv, L.integralNorm_apply,
      smul_eq_mul]
    exact ⟨by ring, by ring⟩
  right_inv p := by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp p.2
    obtain ⟨c₀, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
    have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
    apply Subtype.ext
    dsimp only
    rw [← hab]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, hvv, hvu, huv, L.integralNorm_apply,
      smul_eq_mul]
    have hc₀ : c₀ * 1 + c₁ * L.integralForm u u - L.integralForm u u * (c₀ * 0 + c₁ * 1) = c₀ := by
      ring
    have hc₁ : c₀ * 0 + c₁ * 1 = c₁ := by ring
    rw [hc₀, hc₁]

private theorem bijective_restrict_isotropicPairSpan {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hvu : L.integralForm v u = 1) :
    Function.Bijective (L.integralForm.restrict (isotropicPairSpan L v u)) := by
  let P := isotropicPairSpan L v u
  let e := isotropicPairSpanEquiv hv hvu
  have he0 : (e ![1, 0] : L) = v := by simp [e, isotropicPairSpanEquiv]
  have he1 : (e ![0, 1] : L) = u := by simp [e, isotropicPairSpanEquiv]
  constructor
  · intro p q hpq
    have h0 := LinearMap.congr_fun (sub_eq_zero.mpr hpq) (e ![1, 0])
    have h1 := LinearMap.congr_fun (sub_eq_zero.mpr hpq) (e ![0, 1])
    rw [← map_sub, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.zero_apply, he0] at h0
    rw [← map_sub, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.zero_apply, he1] at h1
    have hsymm : e.symm (p - q) = 0 := by
      ext i
      fin_cases i
      · dsimp only [e, isotropicPairSpanEquiv, LinearEquiv.coe_symm_mk]
        simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.zero_apply]
        rw [h1, h0]
        ring
      · dsimp only [e, isotropicPairSpanEquiv, LinearEquiv.coe_symm_mk]
        simpa only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply]
          using h0
    exact sub_eq_zero.mp ((e.apply_symm_apply (p - q)).symm.trans (by rw [hsymm, map_zero]))
  · intro g
    let g₀ := g (e ![1, 0])
    let g₁ := g (e ![0, 1])
    let p : P := e ![g₁ - L.integralNorm u * g₀, g₀]
    refine ⟨p, LinearMap.ext fun q ↦ ?_⟩
    have hq : q = (e.symm q 0) • e ![1, 0] + (e.symm q 1) • e ![0, 1] := by
      apply e.symm.injective
      rw [map_add, map_smul, map_smul, e.symm_apply_apply, e.symm_apply_apply,
        funext_iff, Fin.forall_fin_two]
      simp
    have hp0 : L.integralForm.restrict P p (e ![1, 0]) = g₀ := by
      have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
      have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, he0]
      simp only [p, e, isotropicPairSpanEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, hvv, huv, smul_eq_mul]
      ring
    have hp1 : L.integralForm.restrict P p (e ![0, 1]) = g₁ := by
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, he1]
      simp only [p, e, isotropicPairSpanEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, hvu, L.integralNorm_apply, smul_eq_mul]
      ring
    rw [hq, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hp0, hp1]

private noncomputable def hyperbolicPlaneIsometryIsotropicPair {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hu : L.integralNorm u = 0) (hvu : L.integralForm v u = 1) :
    Isometry hyperbolicPlane (L.restrictSubmodule (isotropicPairSpan L v u)) := by
  let P := isotropicPairSpan L v u
  let bP : Basis (Fin 2) ℤ (L.restrictSubmodule P) :=
    ((Pi.basisFun ℤ (Fin 2)).map (isotropicPairSpanEquiv hv hvu)).map
      (ofIntegralForm.carrierEquiv (L.integralForm.restrict P) (L.isSymm_integralForm.restrict P))
  have hb0 : (ofIntegralForm.carrierEquiv (L.integralForm.restrict P)
      (L.isSymm_integralForm.restrict P)).symm (bP 0) = ⟨v, Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self v)⟩ := by
    simp [bP, isotropicPairSpanEquiv, Pi.basisFun_apply]
  have hb1 : (ofIntegralForm.carrierEquiv (L.integralForm.restrict P)
      (L.isSymm_integralForm.restrict P)).symm (bP 1) = ⟨u, Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self u)⟩ := by
    simp [bP, isotropicPairSpanEquiv, Pi.basisFun_apply]
  have hgram : hyperbolicPlane.gramMatrix hyperbolicPlaneBasis =
      (L.restrictSubmodule P).gramMatrix bP := by
    rw [gramMatrix_hyperbolicPlaneBasis]
    ext i j
    rw [gramMatrix_apply]
    have hcell := (ofIntegralForm.integralForm_carrierEquiv (L.integralForm.restrict P)
      (L.isSymm_integralForm.restrict P)
      ((ofIntegralForm.carrierEquiv _ _).symm (bP i))
      ((ofIntegralForm.carrierEquiv _ _).symm (bP j))).symm
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hcell
    rw [← hcell]
    have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
    fin_cases i <;> fin_cases j <;>
      simp [hb0, hb1, ← L.integralNorm_apply, hv, hu, hvu, huv]
  exact Isometry.ofGramMatrixEq hyperbolicPlaneBasis bP hgram

/-- **Even hyperbolic splitting.** Every rationally isotropic even unimodular lattice splits off a
hyperbolic plane orthogonally, with an even unimodular complement realized as
`L.restrictSubmodule S` for a carrier submodule `S : Submodule ℤ L`. -/
theorem exists_isometry_hyperbolicPlane_orthogonalSum {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLe : L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ S : Submodule ℤ L,
      (L.restrictSubmodule S).IsUnimodular ∧ (L.restrictSubmodule S).IsEven ∧
        Nonempty (Isometry (hyperbolicPlane.orthogonalSum (L.restrictSubmodule S)) L) := by
  obtain ⟨v, u₀, hv, hvu₀⟩ := exists_integralNorm_eq_zero_integralForm_eq_one hLu hiso
  obtain ⟨k, hk⟩ := (L.even_integralNorm_iff u₀).mpr (L.isEven_iff_forall_norm.mp hLe u₀)
  let u : L := u₀ - k • v
  have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
  have huv₀ : L.integralForm u₀ v = 1 := (L.isSymm_integralForm.eq u₀ v).trans hvu₀
  have hvu : L.integralForm v u = 1 := by
    simp only [u, map_sub, map_smul, hvu₀, hvv, smul_eq_mul]
    ring
  have hu : L.integralNorm u = 0 := by
    have hk' : L.integralForm u₀ u₀ = k + k := by rwa [← L.integralNorm_apply]
    rw [L.integralNorm_apply]
    simp only [u, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      hk', hvu₀, huv₀, hvv, smul_eq_mul]
    ring
  let P := isotropicPairSpan L v u
  let S := L.integralForm.orthogonal P
  let e : Isometry (hyperbolicPlane.orthogonalSum (L.restrictSubmodule S)) L :=
    ((hyperbolicPlaneIsometryIsotropicPair hv hu hvu).orthogonalSum (Isometry.refl _)).trans
      (L.orthogonalSplittingIsometry P (bijective_restrict_isotropicPairSpan hv hvu))
  have hU : (L.restrictSubmodule S).IsUnimodular :=
    ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hLu)).2
  have hE : (L.restrictSubmodule S).IsEven :=
    ((isEven_orthogonalSum_iff _ _).mp (e.isEven_iff.mpr hLe)).2
  exact ⟨S, hU, hE, ⟨e⟩⟩

/-! ## Parity-preserving unit-norm splitting for odd unimodular lattices -/

private theorem exists_odd_integralNorm_integralForm_eq_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ v u : L, L.integralNorm v = 0 ∧ L.integralForm v u = 1 ∧ Odd (L.integralNorm u) := by
  obtain ⟨v, u₀, hv, hvu₀⟩ := exists_integralNorm_eq_zero_integralForm_eq_one hLu hiso
  rcases Int.even_or_odd (L.integralNorm u₀) with hu₀_even | hu₀_odd
  · let P := isotropicPairSpan L v u₀
    have hcompl := L.isCompl_orthogonal_of_restrict_bijective P
      (bijective_restrict_isotropicPairSpan hv hvu₀)
    have hexists_odd : ∃ x : L, Odd (L.integralNorm x) := by
      by_contra h_all
      exact hLo (L.isEven_iff_forall_norm.mpr fun x ↦
        (L.even_integralNorm_iff x).mp (Int.not_odd_iff_even.mp fun hx ↦ h_all ⟨x, hx⟩))
    obtain ⟨x, hx_odd⟩ := hexists_odd
    have hx_sup : x ∈ P ⊔ L.integralForm.orthogonal P := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨p, hpP, z, hzO, rfl⟩ := Submodule.mem_sup.mp hx_sup
    have hp_even : Even (L.integralNorm p) := by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hpP
      obtain ⟨c₀, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨m, hm⟩ := hu₀_even
      have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
      have huv₀ : L.integralForm u₀ v = 1 := (L.isSymm_integralForm.eq u₀ v).trans hvu₀
      have hm' : L.integralForm u₀ u₀ = m + m := by rwa [← L.integralNorm_apply]
      refine ⟨c₀ * c₁ + c₁ ^ 2 * m, ?_⟩
      rw [L.integralNorm_apply]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        hvv, hvu₀, huv₀, hm', smul_eq_mul]
      ring
    have hpz : L.integralForm p z = 0 := hzO p hpP
    have hxz : L.integralNorm (p + z) = L.integralNorm p + L.integralNorm z := by
      rw [L.integralNorm_add, hpz, mul_zero, add_zero]
    have hz_odd : Odd (L.integralNorm z) := by
      obtain ⟨k₁, hk₁⟩ := hp_even
      obtain ⟨k₂, hk₂⟩ := hx_odd
      exact ⟨k₂ - k₁, by omega⟩
    have hvz : L.integralForm v z = 0 :=
      hzO v (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
    have huz : L.integralForm u₀ z = 0 :=
      hzO u₀ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self u₀))
    refine ⟨v, u₀ + z, hv, ?_, ?_⟩
    · rw [map_add, hvu₀, hvz, add_zero]
    · rw [L.integralNorm_add, huz, mul_zero, add_zero]
      exact hu₀_even.add_odd hz_odd
  · exact ⟨v, u₀, hv, hvu₀, hu₀_odd⟩

private theorem exists_orthogonal_unit_pm_vectors {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ xp xm : L, L.integralForm xp xp = 1 ∧ L.integralForm xm xm = -1 ∧
      L.integralForm xp xm = 0 := by
  obtain ⟨v, u, hv, hvu, m, hm⟩ := exists_odd_integralNorm_integralForm_eq_one hLu hLo hiso
  have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
  have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
  have huu : L.integralForm u u = 2 * m + 1 := by rwa [← L.integralNorm_apply]
  refine ⟨u - m • v, u - (m + 1) • v, ?_, ?_, ?_⟩
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      huu, hvu, huv, hvv, smul_eq_mul]
    ring
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      huu, hvu, huv, hvv, smul_eq_mul]
    ring
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      huu, hvu, huv, hvv, smul_eq_mul]
    ring

private theorem not_isEven_restrictSubmodule_of_odd_mem {L : IntegralLattice V}
    (S : Submodule ℤ L) {y : L} (hy : y ∈ S) (hodd : Odd (L.integralForm y y)) :
    ¬ (L.restrictSubmodule S).IsEven := by
  intro hE
  let t : L.restrictSubmodule S :=
    ofIntegralForm.carrierEquiv (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)
      ⟨y, hy⟩
  have ht_norm : (L.restrictSubmodule S).integralNorm t = L.integralForm y y := by
    rw [integralNorm_apply]
    exact ofIntegralForm.integralForm_carrierEquiv (L.integralForm.restrict S)
      (L.isSymm_integralForm.restrict S) ⟨y, hy⟩ ⟨y, hy⟩
  have ht_even := ((L.restrictSubmodule S).even_integralNorm_iff t).mpr
    ((L.restrictSubmodule S).isEven_iff_forall_norm.mp hE t)
  rw [ht_norm] at ht_even
  exact Int.not_odd_iff_even.mpr ht_even hodd

/-- **Parity-preserving `⟨1⟩` splitting.** Every rationally isotropic odd unimodular lattice splits
off `rankOne 1` with an **odd** unimodular orthogonal complement. -/
theorem exists_odd_isUnimodular_rankOne_one_orthogonalSum {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ S : Submodule ℤ L,
      (L.restrictSubmodule S).IsUnimodular ∧ ¬ (L.restrictSubmodule S).IsEven ∧
        Nonempty (Isometry ((rankOne 1).orthogonalSum (L.restrictSubmodule S)) L) := by
  obtain ⟨xp, xm, hxp, hxm, horth⟩ := exists_orthogonal_unit_pm_vectors hLu hLo hiso
  let S := L.integralForm.orthogonal (ℤ ∙ xp)
  have hxp_unit : IsUnit (L.integralForm xp xp) := hxp ▸ isUnit_one
  have hrank : ofGramMatrix (Basis.singleton (Fin 1) ℚ)
      (Matrix.of fun (_ _ : Fin 1) ↦ L.integralForm xp xp) (by ext; rfl) = rankOne 1 :=
    ofGramMatrix_singleton_eq_rankOne 1 hxp (by ext; rfl)
  let e : Isometry ((rankOne 1).orthogonalSum (L.restrictSubmodule S)) L :=
    ((Isometry.ofEq hrank.symm).orthogonalSum (Isometry.refl _)).trans
      (L.unitNormSplittingIsometry xp hxp_unit)
  have hU : (L.restrictSubmodule S).IsUnimodular :=
    ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hLu)).2
  have hxm_mem : xm ∈ S := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, horth, mul_zero]
  have hodd : Odd (L.integralForm xm xm) := hxm ▸ Odd.neg odd_one
  exact ⟨S, hU, not_isEven_restrictSubmodule_of_odd_mem S hxm_mem hodd, ⟨e⟩⟩

/-- **Parity-preserving `⟨-1⟩` splitting.** Every rationally isotropic odd unimodular lattice splits
off `rankOne (-1)` with an **odd** unimodular orthogonal complement. -/
theorem exists_odd_isUnimodular_rankOne_neg_one_orthogonalSum {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ S : Submodule ℤ L,
      (L.restrictSubmodule S).IsUnimodular ∧ ¬ (L.restrictSubmodule S).IsEven ∧
        Nonempty (Isometry ((rankOne (-1)).orthogonalSum (L.restrictSubmodule S)) L) := by
  obtain ⟨xp, xm, hxp, hxm, horth⟩ := exists_orthogonal_unit_pm_vectors hLu hLo hiso
  let S := L.integralForm.orthogonal (ℤ ∙ xm)
  have hxm_unit : IsUnit (L.integralForm xm xm) := hxm ▸ IsUnit.neg isUnit_one
  have hrank : ofGramMatrix (Basis.singleton (Fin 1) ℚ)
      (Matrix.of fun (_ _ : Fin 1) ↦ L.integralForm xm xm) (by ext; rfl) = rankOne (-1) :=
    ofGramMatrix_singleton_eq_rankOne (-1) hxm (by ext; rfl)
  let e : Isometry ((rankOne (-1)).orthogonalSum (L.restrictSubmodule S)) L :=
    ((Isometry.ofEq hrank.symm).orthogonalSum (Isometry.refl _)).trans
      (L.unitNormSplittingIsometry xm hxm_unit)
  have hU : (L.restrictSubmodule S).IsUnimodular :=
    ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hLu)).2
  have hxp_mem : xp ∈ S := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
      (L.isSymm_integralForm.eq xm xp).trans horth, mul_zero]
  have hodd : Odd (L.integralForm xp xp) := hxp ▸ odd_one
  exact ⟨S, hU, not_isEven_restrictSubmodule_of_odd_mem S hxp_mem hodd, ⟨e⟩⟩

/-! ## Unconditional classification of unimodular lattices of signature `(1, 0, 1)` -/

/-- **Every unimodular lattice of signature `(1, 0, 1)` is rationally isotropic.** Any integral
basis of such a lattice has `2 × 2` Gram determinant `-1`, so the quadratic discriminant `4` is an
integral square and produces an explicit nonzero carrier vector of norm zero. -/
theorem not_anisotropic_norm_of_isUnimodular_of_signature_one_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hsig : L.signature = (1, 0, 1)) :
    ¬ L.norm.Anisotropic := by
  have hsp : L.sigPos = 1 ∧ L.sigNull = 0 ∧ L.sigNeg = 1 := by
    simpa only [signature, Prod.mk.injEq] using hsig
  have hdet : L.determinant = -1 := by
    rw [L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsp.2.2,
      L.isUnimodular_iff_discriminant_eq_one.mp hLu]
    norm_num
  have hrank : Module.finrank ℤ L = 2 := by
    rw [L.finrank_carrier, ← L.signature_sum_eq_finrank, hsp.1, hsp.2.1, hsp.2.2]
  let b : Basis (Fin 2) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
  let G := L.gramMatrix b
  have hGsymm : G 1 0 = G 0 1 := (L.isSymm_gramMatrix b).apply 0 1
  have hGdet : G 0 0 * G 1 1 - G 0 1 * G 0 1 = -1 := by
    have hdetG : G.det = -1 := by
      rw [← L.gramDet_def b, ← L.determinant_eq_gramDet b]
      exact hdet
    rw [Matrix.det_fin_two, hGsymm] at hdetG
    exact hdetG
  rw [QuadraticMap.not_anisotropic_iff_exists]
  by_cases h00 : G 0 0 = 0
  · refine ⟨b 0, fun h ↦ b.ne_zero 0 (Subtype.ext h), ?_⟩
    rw [← L.integralNorm_cast, L.integralNorm_apply, ← L.gramMatrix_apply b 0 0]
    exact_mod_cast h00
  · let w : L := (-G 0 1 + 1) • b 0 + G 0 0 • b 1
    have hw_ne : w ≠ 0 := by
      intro hw
      have hrepr := congrArg (fun x ↦ b.repr x 1) hw
      simp [w, h00] at hrepr
    have hw_norm : L.integralNorm w = 0 := by
      have h00' : L.integralForm (b 0) (b 0) = G 0 0 := (L.gramMatrix_apply b 0 0).symm
      have h01' : L.integralForm (b 0) (b 1) = G 0 1 := (L.gramMatrix_apply b 0 1).symm
      have h10' : L.integralForm (b 1) (b 0) = G 0 1 :=
        (L.gramMatrix_apply b 1 0).symm.trans hGsymm
      have h11' : L.integralForm (b 1) (b 1) = G 1 1 := (L.gramMatrix_apply b 1 1).symm
      calc
        L.integralNorm w = G 0 0 * (G 0 0 * G 1 1 - G 0 1 * G 0 1 + 1) := by
          rw [L.integralNorm_apply]
          simp only [w, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            h00', h01', h10', h11', smul_eq_mul]
          ring
        _ = 0 := by rw [hGdet]; ring
    exact ⟨w, fun h ↦ hw_ne (Subtype.ext h),
      by rw [← L.integralNorm_cast, hw_norm, Int.cast_zero]⟩

private noncomputable def orthogonalSumSubsingletonRightIsometry {W : Type*}
    [AddCommGroup W] [Module ℚ W] [Subsingleton W] (A : IntegralLattice V)
    (B : IntegralLattice W) :
    Isometry A (A.orthogonalSum B) := by
  letI : Unique W := uniqueOfSubsingleton 0
  refine
    { toLinearEquiv := (LinearEquiv.prodUnique (R := ℚ) (M := V) (M₂ := W)).symm
      map_app' := fun x y ↦ ?_
      map_carrier := ?_ }
  · have hd : (default : W) = 0 := Subsingleton.elim _ _
    simp [orthogonalSum_form, LinearMap.BilinForm.prod_apply, hd]
  · ext p
    rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.symm_symm,
      LinearEquiv.prodUnique_apply, orthogonalSum_carrier, Submodule.mem_prod]
    exact ⟨fun h ↦ ⟨h, Subsingleton.elim p.2 0 ▸ B.carrier.zero_mem⟩, fun h ↦ h.1⟩

/-- **Classification of even unimodular lattices of signature `(1, 0, 1)`.** Every even unimodular
lattice of signature `(1, 0, 1)` is integrally isometric to `hyperbolicPlane`. -/
theorem nonempty_isometry_hyperbolicPlane_of_isUnimodular_of_signature_one_one
    {L : IntegralLattice V} (hLu : L.IsUnimodular) (hLe : L.IsEven)
    (hsig : L.signature = (1, 0, 1)) :
    Nonempty (Isometry hyperbolicPlane L) := by
  obtain ⟨S, _, _, ⟨e⟩⟩ := exists_isometry_hyperbolicPlane_orthogonalSum hLu hLe
    (not_anisotropic_norm_of_isUnimodular_of_signature_one_one hLu hsig)
  set Y := L.restrictSubmodule S
  have hYrank : Module.finrank ℚ (ℚ ⊗[ℤ] S) = 0 := by
    have hsum := e.signature_eq
    have hU := hyperbolicPlane_signature
    rw [hsig, signature_orthogonalSum] at hsum
    simp only [signature, Prod.mk.injEq] at hU hsum
    have hfin := Y.signature_sum_eq_finrank
    omega
  have : FiniteDimensional ℚ (ℚ ⊗[ℤ] S) := Y.finiteDimensional
  have : Subsingleton (ℚ ⊗[ℤ] S) := Module.finrank_zero_iff.mp hYrank
  exact ⟨(orthogonalSumSubsingletonRightIsometry hyperbolicPlane Y).trans e⟩

/-- **Classification of odd unimodular lattices of signature `(1, 0, 1)`.** Every odd unimodular
lattice of signature `(1, 0, 1)` is integrally isometric to `indefiniteUnitPlane`. -/
theorem nonempty_isometry_indefiniteUnitPlane_of_isUnimodular_of_signature_one_one
    {L : IntegralLattice V} (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven)
    (hsig : L.signature = (1, 0, 1)) :
    Nonempty (Isometry indefiniteUnitPlane L) := by
  obtain ⟨S, hYu, _, ⟨e⟩⟩ := exists_odd_isUnimodular_rankOne_one_orthogonalSum hLu hLo
    (not_anisotropic_norm_of_isUnimodular_of_signature_one_one hLu hsig)
  set Y := L.restrictSubmodule S
  have hsp : Y.sigPos = 0 ∧ Y.sigNull = 0 ∧ Y.sigNeg = 1 := by
    have hsum := e.signature_eq
    have hr1 := rankOne_signature_of_pos (a := 1) zero_lt_one
    rw [hsig, signature_orthogonalSum] at hsum
    simp only [signature, Prod.mk.injEq] at hr1 hsum
    omega
  have hYrank : Module.finrank ℤ Y = 1 := by
    rw [Y.finrank_carrier, ← Y.signature_sum_eq_finrank, hsp.1, hsp.2.1, hsp.2.2]
  have hYdet : Y.determinant = -1 := by
    rw [Y.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsp.2.2,
      Y.isUnimodular_iff_discriminant_eq_one.mp hYu]
    norm_num
  let b : Basis (Fin 1) ℤ Y := Module.finBasisOfFinrankEq ℤ Y hYrank
  have hb0 : Y.integralForm (b 0) (b 0) = -1 := by
    rw [Y.determinant_eq_gramDet b, gramDet_def, Matrix.det_unique, gramMatrix_apply] at hYdet
    exact hYdet
  let G1 : Matrix (Fin 1) (Fin 1) ℤ := Matrix.of fun _ _ ↦ -1
  have hG1 : G1.IsSymm := by ext; rfl
  have hgram : (ofGramMatrix (Basis.singleton (Fin 1) ℚ) G1 hG1).gramMatrix
      (ofGramMatrix.basis (Basis.singleton (Fin 1) ℚ) G1 hG1) = Y.gramMatrix b := by
    rw [gramMatrix_ofGramMatrix]
    ext i j
    fin_cases i
    fin_cases j
    simpa [G1, gramMatrix_apply] using hb0.symm
  let eY : Isometry (rankOne (-1)) Y :=
    (Isometry.ofEq (ofGramMatrix_singleton_eq_rankOne (-1) rfl hG1).symm).trans
      (Isometry.ofGramMatrixEq _ b hgram)
  exact ⟨rankOneOrthogonalSumIsometryIndefiniteUnitPlane.symm.trans
    (((Isometry.refl (rankOne 1)).orthogonalSum eY).trans e)⟩

/-! ## Even-to-odd reduction for indefinite unimodular classification -/

/-- **Even-to-odd reduction for rationally isotropic even unimodular lattices.** Every rationally
isotropic even unimodular lattice `L` is integrally isometric to an explicit even Kneser
two-neighbor `K` of an odd unimodular lattice `(L.restrictSubmodule S).orthogonalSum
indefiniteUnitPlane` of the same signature as `L`. Combined with
`eight_dvd_sub_of_isNeighbor_of_isometry_signedUnitLattice` and
`nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice`, classifying
odd unimodular lattices at signature `(r, 0, s)` immediately yields `8 ∣ (r : ℤ) - s` and
uniqueness up to isometry of rationally isotropic even unimodular lattices at signature
`(r, 0, s)`. -/
theorem exists_odd_isUnimodular_isNeighbor {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLe : L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ (S : Submodule ℤ L) (K : IntegralLattice ((ℚ ⊗[ℤ] S) × (Fin 2 → ℚ))),
      ((L.restrictSubmodule S).orthogonalSum indefiniteUnitPlane).IsUnimodular ∧
        ¬ ((L.restrictSubmodule S).orthogonalSum indefiniteUnitPlane).IsEven ∧
        ((L.restrictSubmodule S).orthogonalSum indefiniteUnitPlane).signature = L.signature ∧
        ((L.restrictSubmodule S).orthogonalSum indefiniteUnitPlane).IsNeighbor K 2 ∧
        K.IsEven ∧ Nonempty (Isometry K L) := by
  obtain ⟨S, hYu, hYe, ⟨e_split⟩⟩ := exists_isometry_hyperbolicPlane_orthogonalSum hLu hLe hiso
  set Y := L.restrictSubmodule S
  let eL : Isometry (Y.orthogonalSum hyperbolicPlane) L :=
    (Isometry.orthogonalSumComm Y hyperbolicPlane).trans e_split
  let N := Y.orthogonalSum indefiniteUnitPlane
  have hNu : N.IsUnimodular :=
    (isUnimodular_orthogonalSum_iff Y indefiniteUnitPlane).mpr
      ⟨hYu, isUnimodular_indefiniteUnitPlane⟩
  have hNo : ¬ N.IsEven := fun h ↦
    not_isEven_indefiniteUnitPlane ((isEven_orthogonalSum_iff Y indefiniteUnitPlane).mp h).2
  have hNsig : N.signature = L.signature := by
    have hL' := eL.signature_eq
    have hU := hyperbolicPlane_signature
    have hI := indefiniteUnitPlane_signature
    rw [signature_orthogonalSum] at hL'
    simp only [N, signature_orthogonalSum]
    simp only [signature, Prod.mk.injEq] at hU hI hL' ⊢
    omega
  obtain ⟨K, hNK, hKe, ⟨eK⟩⟩ := exists_isNeighbor_orthogonalSum_indefiniteUnitPlane hYe
  exact ⟨S, K, hNu, hNo, hNsig, hNK, hKe, ⟨eK.symm.trans eL⟩⟩

end Isotropic

end TauCeti.IntegralLattice
