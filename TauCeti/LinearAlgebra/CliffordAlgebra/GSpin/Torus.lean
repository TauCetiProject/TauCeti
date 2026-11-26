/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GSpin.CliffordGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.HyperbolicPair
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Central scalars and the hyperbolic torus in the general spin group

Let `Q` be a quadratic form over a commutative ring `R`, in every characteristic. This file shows
that the central scalars and the torus of a family of mutually orthogonal hyperbolic pairs lie in
the general spin group `GSpin(Q)` (`CliffordAlgebra.specialCliffordGroup`), and computes their
general spin norm `ν(g) = reverse(g) g`:

* a unit `c` of `R`, viewed as a central scalar, lies in `GSpin(Q)` with `ν(c) = c²`; so the
  scalars with `c² = 1` lie in `Spin(Q) = ker ν` (`CliffordAlgebra.normOneSpinGroup`), and when
  the scalars embed in the Clifford algebra the scalars in `Spin(Q)` are exactly those with
  `c² = 1`. In particular `Spin(Q)` contains `μ₂(R)` in every rank, unlike Mathlib's `spinGroup`,
  which is trivial in rank `0`;
* for a hyperbolic pair `(e, f)` (`Q e = Q f = 0`, `polar Q e f = 1`), the unit
  `u(t) = t e f + f e` lies in `GSpin(Q)`, with `ν(u(t)) = t`, and when `ι` and the scalars embed
  its vector action is the torus `diag(t, t⁻¹)` of the hyperbolic plane
  (`TauCeti.QuadraticMap.hyperbolicPairTorus`);
* for a family `(e_i, f_i)` of mutually orthogonal hyperbolic pairs, the homomorphism
  `(c, a) ↦ c ∏ u_i(a_i)` (`CliffordAlgebra.hyperbolicTorus`) takes values in `GSpin(Q)`
  (`CliffordAlgebra.specialHyperbolicTorus`), with `ν(c ∏ u_i(a_i)) = c² ∏ a_i`, and the
  elements `s⁻¹ u_i(s²)` lie in `Spin(Q)`.

For the standard split forms `TauCeti.splitEvenForm` and `TauCeti.splitOddForm`, whose coordinate
hyperbolic pairs form such a family, this is a split torus of the general spin group, on which the
character `ν` is `2ε₀ + ε₁ + ⋯ + ε_n`; for the odd split form, `s ↦ s⁻¹ u_n(s²)` is the coroot of
`ε_n`.

When the scalars embed in the Clifford algebra and every element of `GSpin(Q)` is a scalar (as in
ranks zero and one), `Spin(Q)` is exactly the group `μ₂(R)` of square roots of unity.

## Main declarations

* `CliffordAlgebra.scalarSpecialCliffordGroup`: the central scalars `Rˣ →* GSpin(Q)`.
* `CliffordAlgebra.specialCliffordGroupNorm_scalarSpecialCliffordGroup`: `ν(c) = c²`.
* `CliffordAlgebra.scalarSpecialCliffordGroup_injective`: the central scalars embed in `GSpin(Q)`
  when they embed in the Clifford algebra.
* `CliffordAlgebra.unitsMap_algebraMap_mem_normOneSpinGroup_iff`: a scalar lies in `Spin(Q)`
  exactly when its square is `1`, when the scalars embed.
* `CliffordAlgebra.normOneSpinGroup_eq_map_rootsOfUnity`: `Spin(Q) = μ₂` when the central scalars
  map bijectively onto `GSpin(Q)`.
* `CliffordAlgebra.hyperbolicPairUnitsHom_mem_specialCliffordGroup`: `u(t) ∈ GSpin(Q)`.
* `CliffordAlgebra.cliffordGroupToOrthogonal_hyperbolicPairUnitsHom`: the vector action of `u(t)`
  is `diag(t, t⁻¹)`.
* `CliffordAlgebra.specialHyperbolicTorus`: the torus `(c, a) ↦ c ∏ u_i(a_i)` as a homomorphism to
  `GSpin(Q)`.
* `CliffordAlgebra.specialCliffordGroupNorm_specialHyperbolicTorus`: `ν(c ∏ u_i(a_i)) = c² ∏ a_i`.
* `CliffordAlgebra.hyperbolicTorus_inv_mulSingle_sq_mem_normOneSpinGroup`: `s⁻¹ u_i(s²) ∈ Spin(Q)`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.4.
* M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002), §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

/-! ### Central scalars -/

section Scalar

variable (Q) in
/-- A unit of the base ring, as a central scalar, lies in the general spin group. -/
theorem unitsMap_algebraMap_mem_specialCliffordGroup (c : Rˣ) :
    Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c ∈
      specialCliffordGroup Q := by
  have hconj (d : Rˣ) (m : M) :
      ((Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) d :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q m *
        ((Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) d)⁻¹ :
          (CliffordAlgebra Q)ˣ) = ι Q m := by
    have hU : ((Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) d :
        (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = algebraMap R _ d := by
      rw [Units.coe_map, MonoidHom.coe_ofClass]
    rw [hU, (Algebra.commute_algebraMap_left (d : R) (ι Q m)).eq, mul_assoc, ← hU,
      Units.mul_inv, mul_one]
  refine mem_specialCliffordGroup_iff_conj.mpr ⟨?_, fun m => ⟨m, (hconj c m).symm⟩,
    fun m => ⟨m, ?_⟩⟩
  · exact Subalgebra.algebraMap_mem _ _
  · have h := hconj c⁻¹ m
    rw [map_inv (Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q)) c,
      inv_inv] at h
    exact h.symm

variable (Q) in
/-- **The central scalars of the general spin group**, `Rˣ →* GSpin(Q)`. -/
noncomputable def scalarSpecialCliffordGroup : Rˣ →* specialCliffordGroup Q :=
  (Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q)).codRestrict _
    (unitsMap_algebraMap_mem_specialCliffordGroup Q)

/-- The central scalar `c` of the general spin group is `algebraMap R _ c`. -/
@[simp]
theorem coe_scalarSpecialCliffordGroup (c : Rˣ) :
    (((scalarSpecialCliffordGroup Q c : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) =
      algebraMap R _ c :=
  (rfl)

/-- The central scalars embed in the general spin group when they embed in the Clifford algebra
(for instance for free `M`, by `CliffordAlgebra.algebraMap_injective_of_free`). -/
theorem scalarSpecialCliffordGroup_injective
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) :
    Function.Injective (scalarSpecialCliffordGroup Q) := fun a b h =>
  Units.ext <| hinj <| by
    rw [← coe_scalarSpecialCliffordGroup, ← coe_scalarSpecialCliffordGroup, h]

/-- **The general spin norm of a central scalar is its square**: `ν(c) = c²`. -/
theorem specialCliffordGroupNorm_scalarSpecialCliffordGroup (c : Rˣ) :
    (((specialCliffordGroupNorm Q (scalarSpecialCliffordGroup Q c) : (CliffordAlgebra Q)ˣ)) :
        CliffordAlgebra Q) = algebraMap R _ ((c : R) ^ 2) := by
  rw [coe_specialCliffordGroupNorm, coe_scalarSpecialCliffordGroup, reverse.commutes, ← map_mul,
    ← pow_two]

/-- A central scalar whose square is `1` lies in `Spin(Q)`. -/
theorem unitsMap_algebraMap_mem_normOneSpinGroup {c : Rˣ} (hc : (c : R) ^ 2 = 1) :
    Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c ∈
      normOneSpinGroup Q := by
  refine mem_normOneSpinGroup_iff.mpr ⟨unitsMap_algebraMap_mem_specialCliffordGroup Q c, ?_⟩
  have h := specialCliffordGroupNorm_scalarSpecialCliffordGroup (Q := Q) c
  rw [coe_specialCliffordGroupNorm, hc, map_one] at h
  exact h

/-- **The scalars in `Spin(Q)` are the square roots of unity**, when the scalars embed in the
Clifford algebra (for instance for free `M`, by `CliffordAlgebra.algebraMap_injective_of_free`).
In particular `Spin(Q)` contains `{±1}` in every rank. -/
theorem unitsMap_algebraMap_mem_normOneSpinGroup_iff
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) (c : Rˣ) :
    Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c ∈
      normOneSpinGroup Q ↔ (c : R) ^ 2 = 1 := by
  refine ⟨fun h => hinj ?_, unitsMap_algebraMap_mem_normOneSpinGroup⟩
  have h2 := specialCliffordGroupNorm_scalarSpecialCliffordGroup (Q := Q) c
  rw [coe_specialCliffordGroupNorm] at h2
  rw [← h2, map_one]
  exact (mem_normOneSpinGroup_iff.mp h).2

/-- **`Spin(Q) = μ₂`** when the scalars embed in the Clifford algebra and every element of the
general spin group is a central scalar: `Spin(Q)` is the image of the square roots of unity. -/
theorem normOneSpinGroup_eq_map_rootsOfUnity
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q)))
    (hsurj : Function.Surjective (scalarSpecialCliffordGroup Q)) :
    normOneSpinGroup Q =
      (rootsOfUnity 2 R).map (Units.map (algebraMap R (CliffordAlgebra Q) : R →* _)) := by
  ext x
  simp only [Subgroup.mem_map, mem_rootsOfUnity]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := hsurj ⟨x, (mem_normOneSpinGroup_iff.mp hx).1⟩
    have hcx : Units.map (algebraMap R (CliffordAlgebra Q) : R →* _) c = x := by
      have h := congrArg Subtype.val hc
      rwa [scalarSpecialCliffordGroup, MonoidHom.codRestrict_apply] at h
    refine ⟨c, Units.ext ?_, hcx⟩
    rw [← hcx] at hx
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (unitsMap_algebraMap_mem_normOneSpinGroup_iff hinj c).mp hx
  · rintro ⟨c, hc, rfl⟩
    exact unitsMap_algebraMap_mem_normOneSpinGroup
      (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one])

end Scalar

/-! ### The torus of a hyperbolic pair -/

section Pair

variable {e f : M}

/-- Conjugation by `u(t)` maps vectors to vectors. -/
private theorem hyperbolicPairUnitsHom_mul_ι_mul_inv_mem_range (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (t : Rˣ) (m : M) :
    ↑(hyperbolicPairUnitsHom he hef t) * ι Q m * ↑(hyperbolicPairUnitsHom he hef t)⁻¹ ∈
      LinearMap.range (ι Q) :=
  ⟨_, (hyperbolicPairUnitsHom_mul_ι_mul_inv he hf hef t m).symm⟩

/-- The unit `u(t)` is even. -/
private theorem coe_hyperbolicPairUnitsHom_mem_even (he : Q e = 0) (hef : polar Q e f = 1)
    (t : Rˣ) :
    ((hyperbolicPairUnitsHom he hef t : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q := by
  rw [coe_hyperbolicPairUnitsHom]
  exact hyperbolicPairScaling_mem_even _

/-- **For a hyperbolic pair, `u(t) = t e f + f e` lies in the general spin group.** -/
theorem hyperbolicPairUnitsHom_mem_specialCliffordGroup (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (t : Rˣ) :
    hyperbolicPairUnitsHom he hef t ∈ specialCliffordGroup Q := by
  refine mem_specialCliffordGroup_iff_conj.mpr ⟨coe_hyperbolicPairUnitsHom_mem_even he hef t,
    hyperbolicPairUnitsHom_mul_ι_mul_inv_mem_range he hf hef t, fun m => ?_⟩
  have h := hyperbolicPairUnitsHom_mul_ι_mul_inv_mem_range he hf hef t⁻¹ m
  rw [map_inv (hyperbolicPairUnitsHom he hef) t, inv_inv] at h
  exact h

/-- The general spin norm of `u(t)` is `ν(u(t)) = t`. -/
theorem specialCliffordGroupNorm_hyperbolicPairUnitsHom (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (t : Rˣ) :
    (((specialCliffordGroupNorm Q
        ⟨hyperbolicPairUnitsHom he hef t,
          hyperbolicPairUnitsHom_mem_specialCliffordGroup he hf hef t⟩ :
        (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) = algebraMap R _ t := by
  rw [coe_specialCliffordGroupNorm, coe_hyperbolicPairUnitsHom,
    reverse_hyperbolicPairScaling_mul_self he hef]

/-- **The vector action of `u(t)` is the torus `diag(t, t⁻¹)` of the hyperbolic plane**, when `ι`
and the scalars embed in the Clifford algebra. -/
theorem cliffordGroupToOrthogonal_hyperbolicPairUnitsHom (hι : Function.Injective (ι Q))
    (hinj : Function.Injective (algebraMap R (CliffordAlgebra Q))) (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (t : Rˣ) :
    cliffordGroupToOrthogonal Q hι hinj
        ⟨hyperbolicPairUnitsHom he hef t, specialCliffordGroup_le_cliffordGroup Q
          (hyperbolicPairUnitsHom_mem_specialCliffordGroup he hf hef t)⟩ =
      TauCeti.QuadraticMap.hyperbolicPairTorus Q he hf hef t := by
  refine Subtype.ext (LinearEquiv.ext fun m => hι ?_)
  rw [ι_cliffordGroupToOrthogonal_apply, Subgroup.coe_mk]
  rw [involute_eq_of_mem_even (coe_hyperbolicPairUnitsHom_mem_even he hef t),
    hyperbolicPairUnitsHom_mul_ι_mul_inv he hf hef t m]

end Pair

/-! ### The torus of a hyperbolic family -/

section Family

variable {κ : Type*} [Fintype κ] {e f : κ → M}

/-- **The torus `c ∏ u_i(a_i)` of a hyperbolic family lies in the general spin group.** -/
theorem hyperbolicTorus_mem_specialCliffordGroup (h : IsHyperbolicFamily Q e f)
    (x : Rˣ × (κ → Rˣ)) : hyperbolicTorus h x ∈ specialCliffordGroup Q := by
  classical
  obtain ⟨c, a⟩ := x
  have hca : hyperbolicTorus h (c, a) =
      Units.map (algebraMap R (CliffordAlgebra Q) : R →* CliffordAlgebra Q) c *
        hyperbolicTorus h (1, a) :=
    Units.ext (by rw [Units.val_mul, coe_hyperbolicTorus, coe_hyperbolicTorus]; simp)
  rw [hca]
  refine mul_mem (unitsMap_algebraMap_mem_specialCliffordGroup Q c) ?_
  rw [← Subgroup.mem_comap (f := hyperbolicTorus h)]
  have hx : ((1, a) : Rˣ × (κ → Rˣ)) = ∏ i, ((1 : Rˣ), Pi.mulSingle i (a i)) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_prod]
    · simp [Prod.snd_prod, Finset.univ_prod_mulSingle]
  rw [hx]
  refine prod_mem fun i _ => ?_
  have hi : hyperbolicTorus h (1, Pi.mulSingle i (a i)) =
      hyperbolicPairUnitsHom (h.left_isotropic i) (h.polar_left_right i) (a i) :=
    Units.ext (by simp)
  rw [Subgroup.mem_comap, hi]
  exact hyperbolicPairUnitsHom_mem_specialCliffordGroup (h.left_isotropic i)
    (h.right_isotropic i) (h.polar_left_right i) (a i)

/-- **The torus of a hyperbolic family in the general spin group**: the homomorphism
`(c, a) ↦ c ∏ u_i(a_i)` from `Rˣ × (κ → Rˣ)` to `GSpin(Q)`. For the standard split forms
`TauCeti.splitEvenForm` and `TauCeti.splitOddForm` this is a split torus of `GSpin(Q)`. -/
noncomputable def specialHyperbolicTorus (h : IsHyperbolicFamily Q e f) :
    Rˣ × (κ → Rˣ) →* specialCliffordGroup Q :=
  (hyperbolicTorus h).codRestrict _ (hyperbolicTorus_mem_specialCliffordGroup h)

/-- The torus of a hyperbolic family in `GSpin(Q)` is `CliffordAlgebra.hyperbolicTorus`. -/
@[simp]
theorem coe_specialHyperbolicTorus (h : IsHyperbolicFamily Q e f) (x : Rˣ × (κ → Rˣ)) :
    (specialHyperbolicTorus h x : (CliffordAlgebra Q)ˣ) = hyperbolicTorus h x :=
  (rfl)

/-- **The general spin norm on the torus** is `ν(c ∏ u_i(a_i)) = c² ∏ a_i`. -/
theorem specialCliffordGroupNorm_specialHyperbolicTorus (h : IsHyperbolicFamily Q e f) (c : Rˣ)
    (a : κ → Rˣ) :
    (((specialCliffordGroupNorm Q (specialHyperbolicTorus h (c, a)) : (CliffordAlgebra Q)ˣ)) :
        CliffordAlgebra Q) = algebraMap R _ ((c : R) ^ 2 * ∏ i, (a i : R)) := by
  rw [coe_specialCliffordGroupNorm, coe_specialHyperbolicTorus, reverse_hyperbolicTorus_mul_self]

/-- **The cocharacter `s ↦ s⁻¹ u_i(s²)` lands in `Spin(Q)`.** -/
theorem hyperbolicTorus_inv_mulSingle_sq_mem_normOneSpinGroup [DecidableEq κ]
    (h : IsHyperbolicFamily Q e f) (i : κ) (s : Rˣ) :
    hyperbolicTorus h (s⁻¹, Pi.mulSingle i (s ^ 2)) ∈ normOneSpinGroup Q :=
  mem_normOneSpinGroup_iff.mpr ⟨hyperbolicTorus_mem_specialCliffordGroup h _,
    reverse_hyperbolicTorus_inv_mulSingle_sq_mul_self h i s⟩

end Family

end CliffordAlgebra
