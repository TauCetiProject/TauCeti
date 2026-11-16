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

Rationally isotropic unimodular integral lattices split off `hyperbolicPlane` (when even) or
`rankOne 1` and `rankOne (-1)` with odd complements (when odd). Unimodular lattices of signature
`(1, 0, 1)` are automatically isotropic and isometric to `hyperbolicPlane` or
`indefiniteUnitPlane`, reducing rationally isotropic even unimodular classification to even Kneser
two-neighbors of odd unimodular lattices.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §§2–5.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

universe u v
variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- An orthogonal direct sum is unimodular if and only if both summands are unimodular. -/
theorem isUnimodular_orthogonalSum_iff (A : IntegralLattice V) (B : IntegralLattice W) :
    (A.orthogonalSum B).IsUnimodular ↔ A.IsUnimodular ∧ B.IsUnimodular := by
  simp only [isUnimodular_iff_discriminant_eq_one, discriminant_orthogonalSum, mul_eq_one]

/-- The integral lattice on `ℚ ⊗[ℤ] S` obtained by rationalizing `L.integralForm.restrict S`. -/
noncomputable abbrev restrictSubmodule (L : IntegralLattice V) (S : Submodule ℤ L) :
    IntegralLattice (ℚ ⊗[ℤ] S) :=
  ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)

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
  have hq : (D : ℚ) * c i = (((c i).num * m : ℤ) : ℚ) := by
    calc (D : ℚ) * c i = (m : ℚ) * (c i * (c i).den) := by
          rw [show D = (c i).den * m from hm]; push_cast; ring
      _ = (((c i).num * m : ℤ) : ℚ) := by rw [Rat.mul_den_eq_num]; push_cast; ring
  rw [L.rationalBasis_apply, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hq, Int.cast_smul_eq_zsmul ℚ]
  exact L.carrier.smul_mem _ (Module.Free.chooseBasis ℤ L i).2

/-- **Rational isotropy ↔ primitive carrier isotropic vector.** -/
theorem not_anisotropic_norm_iff_exists_isPrimitive (L : IntegralLattice V) :
    ¬ L.norm.Anisotropic ↔ ∃ v : L, IsPrimitive v ∧ L.integralNorm v = 0 := by
  rw [QuadraticMap.not_anisotropic_iff_exists]
  refine ⟨fun ⟨x, hx0, hxn⟩ ↦ ?_, fun ⟨v, hv, hvn⟩ ↦
    ⟨v, fun hv0 ↦ hv.ne_zero (Subtype.ext hv0), by rw [← L.integralNorm_cast, hvn, Int.cast_zero]⟩⟩
  obtain ⟨n, hn, hnx⟩ := L.exists_pos_nsmul_mem_carrier x
  let y : L := ⟨n • x, hnx⟩
  have hy0 : y ≠ 0 := fun hy ↦ hx0 ((smul_eq_zero.mp
    ((Nat.cast_smul_eq_nsmul ℚ n x).trans (congrArg Subtype.val hy))).resolve_left
    (Nat.cast_ne_zero.mpr hn.ne'))
  have hyn : L.integralNorm y = 0 := Int.cast_injective (α := ℚ) (by
    rw [L.integralNorm_cast, Int.cast_zero]
    dsimp only [y]; rw [← Nat.cast_smul_eq_nsmul ℚ, QuadraticMap.map_smul, hxn, smul_zero])
  obtain ⟨d, v, hd, hv, hyv⟩ := exists_eq_zsmul_isPrimitive hy0
  rw [hyv, QuadraticMap.map_smul, smul_eq_mul] at hyn
  exact ⟨v, hv, (mul_eq_zero.mp hyn).resolve_left (mul_ne_zero hd.ne' hd.ne')⟩

/-- In a rationally isotropic unimodular lattice, there exist `v, u ∈ L` with `v² = 0` and
`B(v, u) = 1`. -/
theorem exists_integralNorm_eq_zero_integralForm_eq_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hiso : ¬ L.norm.Anisotropic) :
    ∃ v u : L, L.integralNorm v = 0 ∧ L.integralForm v u = 1 := by
  have : L.IsNondegenerate := ⟨hLu.nondegenerate⟩
  obtain ⟨v, hv, hvn⟩ := L.not_anisotropic_norm_iff_exists_isPrimitive.mp hiso
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hv
  let u : L := (L.integralPairingEquiv hLu).symm f
  have h : (L.integralPairingEquiv hLu).toLinearMap u = f :=
    (L.integralPairingEquiv hLu).apply_symm_apply f
  rw [L.integralPairingEquiv_toLinearMap] at h
  exact ⟨v, u, hvn, (L.isSymm_integralForm.eq v u).trans ((LinearMap.congr_fun h v).trans hf)⟩

private def isotropicPairSpan (L : IntegralLattice V) (v u : L) : Submodule ℤ L := ℤ ∙ v ⊔ ℤ ∙ u

private noncomputable def isotropicPairSpanEquiv {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hvu : L.integralForm v u = 1) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] isotropicPairSpan L v u := by
  let f : (Fin 2 → ℤ) → isotropicPairSpan L v u := fun c ↦ ⟨c 0 • v + c 1 • u,
    Submodule.add_mem_sup (Submodule.mem_span_singleton.mpr ⟨c 0, rfl⟩)
      (Submodule.mem_span_singleton.mpr ⟨c 1, rfl⟩)⟩
  let g : isotropicPairSpan L v u → (Fin 2 → ℤ) := fun p ↦
    ![L.integralForm p.1 u - L.integralNorm u * L.integralForm p.1 v, L.integralForm p.1 v]
  have hleft : Function.LeftInverse g f := fun c ↦ by
    have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
    have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
    refine funext (Fin.forall_fin_two.mpr ?_)
    simp only [f, g, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, hvv, hvu, huv, L.integralNorm_apply, smul_eq_mul]
    exact ⟨by ring, by ring⟩
  exact
    { toFun := f, invFun := g
      map_add' := fun c d ↦ Subtype.ext (by
        simp only [f, Pi.add_apply, add_smul, Submodule.coe_add]; abel)
      map_smul' := fun r c ↦ Subtype.ext (by
        simp only [f, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Submodule.coe_smul, smul_add,
          mul_smul])
      left_inv := hleft
      right_inv := fun p ↦ by
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp p.2
        obtain ⟨c₀, rfl⟩ := Submodule.mem_span_singleton.mp ha
        obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hb
        exact (show p = f ![c₀, c₁] from Subtype.ext hab.symm).symm ▸ congrArg f (hleft ![c₀, c₁]) }

private noncomputable def isotropicPairBasis {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hvu : L.integralForm v u = 1) :
    Basis (Fin 2) ℤ (L.restrictSubmodule (isotropicPairSpan L v u)) :=
  ((Pi.basisFun ℤ (Fin 2)).map (isotropicPairSpanEquiv hv hvu)).map
    (ofIntegralForm.carrierEquiv (L.integralForm.restrict _) (L.isSymm_integralForm.restrict _))

private theorem gramMatrix_isotropicPairBasis {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hvu : L.integralForm v u = 1) :
    (L.restrictSubmodule (isotropicPairSpan L v u)).gramMatrix (isotropicPairBasis hv hvu) =
      !![0, 1; 1, L.integralNorm u] := by
  let P := isotropicPairSpan L v u
  let e := ofIntegralForm.carrierEquiv (L.integralForm.restrict P)
    (L.isSymm_integralForm.restrict P)
  have hb (i : Fin 2) : (e.symm (isotropicPairBasis hv hvu i)).1 = ![v, u] i := by
    fin_cases i <;> simp [isotropicPairBasis, e, P, isotropicPairSpanEquiv, Pi.basisFun_apply]
  have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
  ext i j; rw [gramMatrix_apply]
  have hcell := (ofIntegralForm.integralForm_carrierEquiv (L.integralForm.restrict P)
    (L.isSymm_integralForm.restrict P) (e.symm (isotropicPairBasis hv hvu i))
    (e.symm (isotropicPairBasis hv hvu j))).symm
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hcell
  rw [← hcell, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  fin_cases i <;> fin_cases j <;> simp [hb, ← L.integralNorm_apply, hv, hvu, huv]

private theorem bijective_restrict_isotropicPairSpan {L : IntegralLattice V} {v u : L}
    (hv : L.integralNorm v = 0) (hvu : L.integralForm v u = 1) :
    Function.Bijective (L.integralForm.restrict (isotropicPairSpan L v u)) := by
  let P := isotropicPairSpan L v u
  have hU : (L.restrictSubmodule P).IsUnimodular := by
    rw [(L.restrictSubmodule P).isUnimodular_iff_isUnit_gramDet (isotropicPairBasis hv hvu),
      gramDet_def, gramMatrix_isotropicPairBasis hv hvu, Matrix.det_fin_two]; simp
  have : (L.restrictSubmodule P).IsNondegenerate := ⟨hU.nondegenerate⟩
  let e := ofIntegralForm.carrierEquiv (L.integralForm.restrict P)
    (L.isSymm_integralForm.restrict P)
  have hfactor : (L.integralForm.restrict P : P → P →ₗ[ℤ] ℤ) =
      (e.arrowCongr (LinearEquiv.refl ℤ ℤ)).symm ∘ (L.restrictSubmodule P).integralForm ∘ e :=
    funext fun p ↦ LinearMap.ext fun q ↦ by simp [e]
  rw [hfactor]
  exact (e.arrowCongr (LinearEquiv.refl ℤ ℤ)).symm.bijective.comp
    (((L.restrictSubmodule P).isUnimodular_iff_integralForm_bijective.mp hU).comp e.bijective)

/-- **Even hyperbolic splitting.** -/
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
  have hvu : L.integralForm v u = 1 := by simp [u, hvu₀, hvv]
  have hu : L.integralNorm u = 0 := by
    have hk' : L.integralForm u₀ u₀ = k + k := by rwa [← L.integralNorm_apply]
    rw [L.integralNorm_apply]; simp only [u, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, hk', hvu₀, huv₀, hvv, smul_eq_mul]; ring
  let eU : Isometry hyperbolicPlane (L.restrictSubmodule (isotropicPairSpan L v u)) :=
    Isometry.ofGramMatrixEq hyperbolicPlaneBasis (isotropicPairBasis hv hvu)
      (gramMatrix_hyperbolicPlaneBasis.trans (by rw [gramMatrix_isotropicPairBasis, hu]))
  let e := (eU.orthogonalSum (Isometry.refl _)).trans
    (L.orthogonalSplittingIsometry _ (bijective_restrict_isotropicPairSpan hv hvu))
  exact ⟨_, ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hLu)).2,
    ((isEven_orthogonalSum_iff _ _).mp (e.isEven_iff.mpr hLe)).2, ⟨e⟩⟩

private theorem exists_odd_integralNorm_integralForm_eq_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ v u : L, L.integralNorm v = 0 ∧ L.integralForm v u = 1 ∧ Odd (L.integralNorm u) := by
  obtain ⟨v, u₀, hv, hvu₀⟩ := exists_integralNorm_eq_zero_integralForm_eq_one hLu hiso
  rcases Int.even_or_odd (L.integralNorm u₀) with ⟨m, hm⟩ | hu₀_odd
  · let P := isotropicPairSpan L v u₀
    have hcompl := L.isCompl_orthogonal_of_restrict_bijective P
      (bijective_restrict_isotropicPairSpan hv hvu₀)
    obtain ⟨x, hx_odd⟩ : ∃ x : L, Odd (L.integralNorm x) := by_contra fun h ↦ hLo
      (L.isEven_iff_forall_norm.mpr fun x ↦ (L.even_integralNorm_iff x).mp
        (Int.not_odd_iff_even.mp fun hx ↦ h ⟨x, hx⟩))
    obtain ⟨p, hpP, z, hzO, rfl⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top.symm ▸ trivial :
      x ∈ P ⊔ L.integralForm.orthogonal P)
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hpP
    obtain ⟨c₀, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
    have huv₀ : L.integralForm u₀ v = 1 := (L.isSymm_integralForm.eq u₀ v).trans hvu₀
    have hm' : L.integralForm u₀ u₀ = m + m := by rwa [← L.integralNorm_apply]
    obtain ⟨k₁, hk₁⟩ : Even (L.integralNorm (c₀ • v + c₁ • u₀)) := ⟨c₀ * c₁ + c₁ ^ 2 * m, by
      rw [L.integralNorm_apply]; simp only [map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, hvv, hvu₀, huv₀, hm', smul_eq_mul]; ring⟩
    rw [L.integralNorm_add, hzO _ hpP, mul_zero, add_zero] at hx_odd; obtain ⟨k₂, hk₂⟩ := hx_odd
    refine ⟨v, u₀ + z, hv, ?_, ?_⟩
    · simp [hvu₀, hzO v (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))]
    · rw [L.integralNorm_add, hzO u₀ (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self u₀)), mul_zero, add_zero]
      exact Even.add_odd ⟨m, hm⟩ ⟨k₂ - k₁, by omega⟩
  · exact ⟨v, u₀, hv, hvu₀, hu₀_odd⟩

private theorem exists_orthogonal_unit_pm_vectors {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ xp xm : L, L.integralForm xp xp = 1 ∧ L.integralForm xm xm = -1 ∧
      L.integralForm xp xm = 0 := by
  obtain ⟨v, u, hv, hvu, m, hm⟩ := exists_odd_integralNorm_integralForm_eq_one hLu hLo hiso
  have hvv : L.integralForm v v = 0 := by rwa [← L.integralNorm_apply]
  have huv : L.integralForm u v = 1 := (L.isSymm_integralForm.eq u v).trans hvu
  have huu : L.integralForm u u = 2 * m + 1 := by rwa [← L.integralNorm_apply]
  refine ⟨u - m • v, u - (m + 1) • v, ?_, ?_, ?_⟩ <;>
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, huu, hvu, huv, hvv,
      smul_eq_mul] <;> ring

private theorem exists_odd_isUnimodular_rankOne_orthogonalSum_of_pm {L : IntegralLattice V}
    (hLu : L.IsUnimodular) {a : ℤ} {x y : L} (hx : L.integralForm x x = a) (ha : IsUnit a)
    (hy : Odd (L.integralForm y y)) (hxy : L.integralForm x y = 0) :
    ∃ S : Submodule ℤ L,
      (L.restrictSubmodule S).IsUnimodular ∧ ¬ (L.restrictSubmodule S).IsEven ∧
        Nonempty (Isometry ((rankOne a).orthogonalSum (L.restrictSubmodule S)) L) := by
  let S := L.integralForm.orthogonal (ℤ ∙ x)
  have hr1 := (ofGramMatrix_singleton_eq_rankOne a hx (by ext; rfl)).symm
  let e := ((Isometry.ofEq hr1).orthogonalSum (Isometry.refl _)).trans
    (L.unitNormSplittingIsometry x (hx ▸ ha))
  have hyS : y ∈ S := LinearMap.BilinForm.mem_orthogonal_iff.mpr fun z hz ↦ by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz; simp [hxy]
  refine ⟨S, ((isUnimodular_orthogonalSum_iff _ _).mp (e.isUnimodular_iff.mpr hLu)).2, fun hE ↦ ?_,
    ⟨e⟩⟩
  let t := ofIntegralForm.carrierEquiv (L.integralForm.restrict S)
    (L.isSymm_integralForm.restrict S) ⟨y, hyS⟩
  have ht : (L.restrictSubmodule S).integralNorm t = L.integralForm y y :=
    ((L.restrictSubmodule S).integralNorm_apply t).trans (ofIntegralForm.integralForm_carrierEquiv
      (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S) ⟨y, hyS⟩ ⟨y, hyS⟩)
  exact Int.not_odd_iff_even.mpr (ht ▸ ((L.restrictSubmodule S).even_integralNorm_iff t).mpr
    ((L.restrictSubmodule S).isEven_iff_forall_norm.mp hE t)) hy

/-- **Parity-preserving `⟨1⟩` splitting.** -/
theorem exists_odd_isUnimodular_rankOne_one_orthogonalSum {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ S : Submodule ℤ L,
      (L.restrictSubmodule S).IsUnimodular ∧ ¬ (L.restrictSubmodule S).IsEven ∧
        Nonempty (Isometry ((rankOne 1).orthogonalSum (L.restrictSubmodule S)) L) := by
  obtain ⟨xp, xm, hxp, hxm, horth⟩ := exists_orthogonal_unit_pm_vectors hLu hLo hiso
  exact exists_odd_isUnimodular_rankOne_orthogonalSum_of_pm hLu hxp isUnit_one
    (hxm ▸ Odd.neg odd_one) horth

/-- **Parity-preserving `⟨-1⟩` splitting.** -/
theorem exists_odd_isUnimodular_rankOne_neg_one_orthogonalSum {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven) (hiso : ¬ L.norm.Anisotropic) :
    ∃ S : Submodule ℤ L,
      (L.restrictSubmodule S).IsUnimodular ∧ ¬ (L.restrictSubmodule S).IsEven ∧
        Nonempty (Isometry ((rankOne (-1)).orthogonalSum (L.restrictSubmodule S)) L) := by
  obtain ⟨xp, xm, hxp, hxm, horth⟩ := exists_orthogonal_unit_pm_vectors hLu hLo hiso
  exact exists_odd_isUnimodular_rankOne_orthogonalSum_of_pm hLu hxm (IsUnit.neg isUnit_one)
    (hxp ▸ odd_one) ((L.isSymm_integralForm.eq xm xp).trans horth)

/-- **Every unimodular lattice of signature `(1, 0, 1)` is rationally isotropic.** -/
theorem not_anisotropic_norm_of_isUnimodular_of_signature_one_one {L : IntegralLattice V}
    (hLu : L.IsUnimodular) (hsig : L.signature = (1, 0, 1)) : ¬ L.norm.Anisotropic := by
  have hsp : L.sigPos = 1 ∧ L.sigNull = 0 ∧ L.sigNeg = 1 := by simpa [signature] using hsig
  have hrank : Module.finrank ℤ L = 2 := by
    rw [L.finrank_carrier, ← L.signature_sum_eq_finrank, hsp.1, hsp.2.1, hsp.2.2]
  let b : Basis (Fin 2) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
  let G := L.gramMatrix b
  have hGsymm : G 1 0 = G 0 1 := (L.isSymm_gramMatrix b).apply 0 1
  have hGdet : G 0 0 * G 1 1 - G 0 1 * G 0 1 = -1 := by
    have hdet : G.det = -1 := by
      rw [← L.gramDet_def b, ← L.determinant_eq_gramDet b,
        L.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsp.2.2,
        L.isUnimodular_iff_discriminant_eq_one.mp hLu]; norm_num
    rwa [Matrix.det_fin_two, hGsymm] at hdet
  rw [QuadraticMap.not_anisotropic_iff_exists]
  by_cases h00 : G 0 0 = 0
  · refine ⟨b 0, fun h ↦ b.ne_zero 0 (Subtype.ext h), ?_⟩
    rw [← L.integralNorm_cast, L.integralNorm_apply, ← L.gramMatrix_apply b 0 0]; exact_mod_cast h00
  · let w : L := (-G 0 1 + 1) • b 0 + G 0 0 • b 1
    have hw_ne : w ≠ 0 := fun hw ↦ by simpa [w, h00] using congrArg (fun x ↦ b.repr x 1) hw
    have hw_norm : L.integralNorm w = 0 := by
      rw [L.integralNorm_apply]
      simp only [w, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        ← L.gramMatrix_apply b, smul_eq_mul]
      linear_combination G 0 0 * hGdet + ((-G 0 1 + 1) * G 0 0) * hGsymm
    exact ⟨w, fun h ↦ hw_ne (Subtype.ext h), by rw [← L.integralNorm_cast, hw_norm, Int.cast_zero]⟩

private noncomputable def orthogonalSumSubsingletonRightIsometry [Subsingleton W]
    (A : IntegralLattice V) (B : IntegralLattice W) : Isometry A (A.orthogonalSum B) := by
  letI : Unique W := uniqueOfSubsingleton 0
  refine { toLinearEquiv := (LinearEquiv.prodUnique (R := ℚ) (M := V) (M₂ := W)).symm
           map_app' := fun x y ↦ by
             simp [orthogonalSum_form, LinearMap.BilinForm.prod_apply,
               Subsingleton.elim (default : W) 0]
           map_carrier := Submodule.ext fun p ↦ ?_ }
  rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.symm_symm,
    LinearEquiv.prodUnique_apply, orthogonalSum_carrier, Submodule.mem_prod]
  exact ⟨fun h ↦ ⟨h, Subsingleton.elim p.2 0 ▸ B.carrier.zero_mem⟩, fun h ↦ h.1⟩

/-- **Classification of even unimodular lattices of signature `(1, 0, 1)`.** -/
theorem nonempty_isometry_hyperbolicPlane_of_isUnimodular_of_signature_one_one
    {L : IntegralLattice V} (hLu : L.IsUnimodular) (hLe : L.IsEven)
    (hsig : L.signature = (1, 0, 1)) : Nonempty (Isometry hyperbolicPlane L) := by
  obtain ⟨S, _, _, ⟨e⟩⟩ := exists_isometry_hyperbolicPlane_orthogonalSum hLu hLe
    (not_anisotropic_norm_of_isUnimodular_of_signature_one_one hLu hsig)
  set Y := L.restrictSubmodule S
  have hYrank : Module.finrank ℚ (ℚ ⊗[ℤ] S) = 0 := by
    have hsum := e.signature_eq; have hU := hyperbolicPlane_signature
    rw [hsig, signature_orthogonalSum] at hsum; simp only [signature, Prod.mk.injEq] at hU hsum
    have := Y.signature_sum_eq_finrank; omega
  have : FiniteDimensional ℚ (ℚ ⊗[ℤ] S) := Y.finiteDimensional
  have : Subsingleton (ℚ ⊗[ℤ] S) := Module.finrank_zero_iff.mp hYrank
  exact ⟨(orthogonalSumSubsingletonRightIsometry hyperbolicPlane Y).trans e⟩

/-- **Classification of odd unimodular lattices of signature `(1, 0, 1)`.** -/
theorem nonempty_isometry_indefiniteUnitPlane_of_isUnimodular_of_signature_one_one
    {L : IntegralLattice V} (hLu : L.IsUnimodular) (hLo : ¬ L.IsEven)
    (hsig : L.signature = (1, 0, 1)) : Nonempty (Isometry indefiniteUnitPlane L) := by
  obtain ⟨S, hYu, _, ⟨e⟩⟩ := exists_odd_isUnimodular_rankOne_one_orthogonalSum hLu hLo
    (not_anisotropic_norm_of_isUnimodular_of_signature_one_one hLu hsig)
  set Y := L.restrictSubmodule S
  have hsp : Y.sigPos = 0 ∧ Y.sigNull = 0 ∧ Y.sigNeg = 1 := by
    have hsum := e.signature_eq; have hr1 := rankOne_signature_of_pos (a := 1) zero_lt_one
    rw [hsig, signature_orthogonalSum] at hsum; simp only [signature, Prod.mk.injEq] at hr1 hsum
    omega
  have hYrank : Module.finrank ℤ Y = 1 := by
    rw [Y.finrank_carrier, ← Y.signature_sum_eq_finrank, hsp.1, hsp.2.1, hsp.2.2]
  let b : Basis (Fin 1) ℤ Y := Module.finBasisOfFinrankEq ℤ Y hYrank
  have hb0 : Y.integralForm (b 0) (b 0) = -1 := by
    have hYdet : Y.determinant = -1 := by
      rw [Y.determinant_eq_neg_one_pow_sigNeg_mul_discriminant, hsp.2.2,
        Y.isUnimodular_iff_discriminant_eq_one.mp hYu]; norm_num
    rwa [Y.determinant_eq_gramDet b, gramDet_def, Matrix.det_unique, gramMatrix_apply] at hYdet
  let G1 : Matrix (Fin 1) (Fin 1) ℤ := Matrix.of fun _ _ ↦ -1
  have hG1 : G1.IsSymm := by ext; rfl
  let eY : Isometry (rankOne (-1)) Y :=
    (Isometry.ofEq (ofGramMatrix_singleton_eq_rankOne (-1) rfl hG1).symm).trans
      (Isometry.ofGramMatrixEq (ofGramMatrix.basis (Basis.singleton (Fin 1) ℚ) G1 hG1) b (by
        rw [gramMatrix_ofGramMatrix]; ext i j; fin_cases i; fin_cases j
        simpa [G1, gramMatrix_apply] using hb0.symm))
  exact ⟨rankOneOrthogonalSumIsometryIndefiniteUnitPlane.symm.trans
    (((Isometry.refl (rankOne 1)).orthogonalSum eY).trans e)⟩

/-- **Even-to-odd reduction for rationally isotropic even unimodular lattices.** -/
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
  let eL := (Isometry.orthogonalSumComm Y hyperbolicPlane).trans e_split
  let N := Y.orthogonalSum indefiniteUnitPlane
  have hNsig : N.signature = L.signature := by
    have hL' := eL.signature_eq; have hU := hyperbolicPlane_signature
    have hI := indefiniteUnitPlane_signature; rw [signature_orthogonalSum] at hL'
    simp only [N, signature_orthogonalSum, signature, Prod.mk.injEq] at hU hI hL' ⊢; omega
  obtain ⟨K, hNK, hKe, ⟨eK⟩⟩ := exists_isNeighbor_orthogonalSum_indefiniteUnitPlane hYe
  exact ⟨S, K, (isUnimodular_orthogonalSum_iff _ _).mpr ⟨hYu, isUnimodular_indefiniteUnitPlane⟩,
    fun h ↦ not_isEven_indefiniteUnitPlane ((isEven_orthogonalSum_iff _ _).mp h).2,
    hNsig, hNK, hKe, ⟨eK.symm.trans eL⟩⟩

end TauCeti.IntegralLattice
