/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.HyperbolicPair
import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Odd

/-!
# The torus of a hyperbolic pair in the Clifford algebra

Let `Q` be a quadratic form over a commutative ring `R`, with un-halved polar form `B = polar Q`,
and let `e`, `f` be a *hyperbolic pair*: `Q e = Q f = 0` and `B e f = 1`. In the Clifford algebra
`C(Q)`, the elements `e f` and `f e` are orthogonal idempotents with sum `1`, both even. Put

`u(a) = a e f + f e`.

Then `a ↦ u(a)` is multiplicative, so `u` restricts to a homomorphism `Rˣ →* C(Q)ˣ`. A unit `u(t)`
conjugates `e` to `t e` and `f` to `t⁻¹ f`, and commutes with every vector orthogonal to both; so
its vector action is `TauCeti.QuadraticMap.hyperbolicPairTorus`, the diagonal torus
`diag(t, t⁻¹)` of the hyperbolic plane. Its Clifford norm is `τ(u(a)) u(a) = a`, where
`τ = CliffordAlgebra.reverse`.

For a family of mutually orthogonal hyperbolic pairs `(e_i, f_i)`, the elements `u_i(a_i)`
commute, and `(c, a) ↦ c ∏ u_i(a_i)` is a homomorphism `Rˣ × (ι → Rˣ) →* C(Q)ˣ` with Clifford
norm `c² ∏ a_i`. The coordinate hyperbolic pairs of `TauCeti.splitEvenForm` and
`TauCeti.splitOddForm` form such families. This is the torus of the general spin group of the
standard split forms of ReductiveGroups §9B.7; on `𝔾_m` its value `c` is the central cocharacter
`ε₀∨`, and for an odd split form `s ↦ s⁻¹ u_n(s²)` has norm one.

## Main definitions

* `CliffordAlgebra.hyperbolicPairScaling Q e f a`: the element `u(a) = a e f + f e`.
* `CliffordAlgebra.hyperbolicPairUnitsHom he hef`: the homomorphism `t ↦ u(t)` from `Rˣ` to
  the units of `C(Q)`.
* `TauCeti.QuadraticMap.IsHyperbolicFamily Q e f`: `(e_i, f_i)` is a family of mutually
  orthogonal hyperbolic pairs.
* `CliffordAlgebra.hyperbolicTorus h`: the homomorphism `(c, a) ↦ c ∏ u_i(a_i)`.

## Main results

* `CliffordAlgebra.ι_mul_ι_add_ι_mul_ι_of_polar_eq_one`: `e f + f e = 1`.
* `CliffordAlgebra.isIdempotentElem_ι_mul_ι`, `CliffordAlgebra.ι_mul_ι_mul_ι_mul_ι_swap`:
  `e f` and `f e` are orthogonal idempotents.
* `CliffordAlgebra.hyperbolicPairScaling_mem_even`: `u(a)` lies in the even subalgebra.
* `CliffordAlgebra.hyperbolicPairScaling_mul`: `u(a b) = u(a) u(b)`.
* `CliffordAlgebra.hyperbolicPairUnitsHom_mul_ι_left_mul_inv`,
  `CliffordAlgebra.hyperbolicPairUnitsHom_mul_ι_right_mul_inv`: `u(t) e u(t)⁻¹ = t e` and
  `u(t) f u(t)⁻¹ = t⁻¹ f`.
* `CliffordAlgebra.hyperbolicPairUnitsHom_mul_ι_mul_inv`: the vector action of `u(t)` is
  `TauCeti.QuadraticMap.hyperbolicPairTorus`.
* `CliffordAlgebra.reverse_hyperbolicPairScaling_mul_self`: `τ(u(a)) u(a) = a`.
* `CliffordAlgebra.commute_hyperbolicPairScaling_of_ne`: the `u_i` of different pairs commute.
* `CliffordAlgebra.reverse_hyperbolicTorus_mul_self`: the Clifford norm of `c ∏ u_i(a_i)` is
  `c² ∏ a_i`.
* `CliffordAlgebra.reverse_hyperbolicTorus_inv_mulSingle_sq_mul_self`: `s⁻¹ u_i(s²)` has norm
  one.
* `TauCeti.isHyperbolicFamily_splitEvenForm`, `TauCeti.isHyperbolicFamily_splitOddForm`: the
  coordinate hyperbolic pairs of the standard split forms.

## References

* B. Conrad, *Reductive group schemes*, Appendix C.4.
* M. Asgari, *Local L-functions for split spinor groups*, Canad. J. Math. 54 (2002), §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}

section Pair

variable {e f : M}

/-- For a pair with `polar Q e f = 1`, `e f + f e = 1` in the Clifford algebra. -/
theorem ι_mul_ι_add_ι_mul_ι_of_polar_eq_one (hef : polar Q e f = 1) :
    ι Q e * ι Q f + ι Q f * ι Q e = 1 := by
  rw [ι_mul_ι_add_swap, hef, map_one]

/-- The product `(e f) (f e)` is the scalar `Q e * Q f`. -/
theorem ι_mul_ι_mul_ι_mul_ι_swap (e f : M) :
    ι Q e * ι Q f * (ι Q f * ι Q e) = algebraMap R _ (Q e * Q f) := by
  rw [mul_assoc, ← mul_assoc (ι Q f), ι_sq_scalar, Algebra.left_comm, ι_sq_scalar,
    ← (algebraMap R (CliffordAlgebra Q)).map_mul, mul_comm]

/-- For a pair with `polar Q e f = 1` and `Q e * Q f = 0` (for instance, one of the two vectors
isotropic), the element `e f` is idempotent. -/
theorem isIdempotentElem_ι_mul_ι (hef : polar Q e f = 1) (h : Q e * Q f = 0) :
    IsIdempotentElem (ι Q e * ι Q f) := by
  have h' : ι Q f * ι Q e = 1 - ι Q e * ι Q f :=
    eq_sub_of_add_eq' (ι_mul_ι_add_ι_mul_ι_of_polar_eq_one hef)
  calc ι Q e * ι Q f * (ι Q e * ι Q f) = ι Q e * (ι Q f * ι Q e) * ι Q f := by
        simp only [mul_assoc]
    _ = ι Q e * ι Q f := by
        rw [h']
        simp only [mul_sub, sub_mul, mul_one, mul_assoc]
        rw [ι_sq_scalar, ← mul_assoc, ι_sq_scalar, ← (algebraMap R (CliffordAlgebra Q)).map_mul, h,
          map_zero, sub_zero]

/-- The four relations among `E = e f` and `F = f e` for `Q e = 0` and `polar Q e f = 1`:
both are idempotent and they are orthogonal. -/
private theorem hyperbolic_relations (he : Q e = 0) (hef : polar Q e f = 1) :
    ι Q e * ι Q f * (ι Q e * ι Q f) = ι Q e * ι Q f ∧
      ι Q f * ι Q e * (ι Q f * ι Q e) = ι Q f * ι Q e ∧
      ι Q e * ι Q f * (ι Q f * ι Q e) = 0 ∧ ι Q f * ι Q e * (ι Q e * ι Q f) = 0 := by
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  refine ⟨(isIdempotentElem_ι_mul_ι hef (by rw [he, zero_mul])).eq,
    (isIdempotentElem_ι_mul_ι hfe (by rw [he, mul_zero])).eq, ?_, ?_⟩ <;>
    rw [ι_mul_ι_mul_ι_mul_ι_swap, he] <;> simp

/-- An isotropic vector squares to zero, also inside a product. -/
private theorem ι_mul_ι_mul_eq_zero {x : M} (hx : Q x = 0) (y : CliffordAlgebra Q) :
    ι Q x * (ι Q x * y) = 0 := by
  rw [← mul_assoc, ι_sq_scalar, hx, map_zero, zero_mul]

variable (Q) in
/-- The element `u(a) = a e f + f e` of the Clifford algebra attached to a pair of vectors. For a
hyperbolic pair it scales `e` by `a` and `f` by `a⁻¹` under conjugation. -/
@[expose] noncomputable def hyperbolicPairScaling (e f : M) (a : R) : CliffordAlgebra Q :=
  a • (ι Q e * ι Q f) + ι Q f * ι Q e

/-- The element `u(a)` is even. -/
theorem hyperbolicPairScaling_mem_even (a : R) :
    hyperbolicPairScaling Q e f a ∈ even Q :=
  add_mem (Subalgebra.smul_mem _ (ι_mul_ι_mem_evenOdd_zero Q e f) a)
    (ι_mul_ι_mem_evenOdd_zero Q f e)

/-- The grade involution fixes `u(a)`. -/
@[simp]
theorem involute_hyperbolicPairScaling (a : R) :
    involute (hyperbolicPairScaling Q e f a) = hyperbolicPairScaling Q e f a :=
  involute_eq_of_mem_even (hyperbolicPairScaling_mem_even a)

/-- For `polar Q e f = 1`, `u(1) = 1`. -/
theorem hyperbolicPairScaling_one (hef : polar Q e f = 1) :
    hyperbolicPairScaling Q e f 1 = 1 := by
  rw [hyperbolicPairScaling, one_smul, ι_mul_ι_add_ι_mul_ι_of_polar_eq_one hef]

/-- For a hyperbolic pair, `u(a b) = u(a) u(b)`. -/
theorem hyperbolicPairScaling_mul (he : Q e = 0) (hef : polar Q e f = 1) (a b : R) :
    hyperbolicPairScaling Q e f (a * b) =
      hyperbolicPairScaling Q e f a * hyperbolicPairScaling Q e f b := by
  obtain ⟨hE, hF, hEF, hFE⟩ := hyperbolic_relations he hef
  simp only [hyperbolicPairScaling, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hE, hF,
    hEF, hFE, smul_zero, add_zero, zero_add, smul_smul, mul_comm b a]

/-- For a hyperbolic pair, `a ↦ u(a)` as a monoid homomorphism. -/
@[expose] noncomputable def hyperbolicPairScalingHom (he : Q e = 0) (hef : polar Q e f = 1) :
    R →* CliffordAlgebra Q where
  toFun := hyperbolicPairScaling Q e f
  map_one' := hyperbolicPairScaling_one hef
  map_mul' := hyperbolicPairScaling_mul he hef

@[simp]
theorem hyperbolicPairScalingHom_apply (he : Q e = 0) (hef : polar Q e f = 1) (a : R) :
    hyperbolicPairScalingHom he hef a = hyperbolicPairScaling Q e f a :=
  rfl

/-- For a hyperbolic pair, `t ↦ u(t)` as a homomorphism from `Rˣ` to the units of the Clifford
algebra. -/
@[expose] noncomputable def hyperbolicPairUnitsHom (he : Q e = 0) (hef : polar Q e f = 1) :
    Rˣ →* (CliffordAlgebra Q)ˣ :=
  Units.map (hyperbolicPairScalingHom he hef)

@[simp]
theorem coe_hyperbolicPairUnitsHom (he : Q e = 0) (hef : polar Q e f = 1) (t : Rˣ) :
    (hyperbolicPairUnitsHom he hef t : CliffordAlgebra Q) =
      hyperbolicPairScaling Q e f t :=
  rfl

@[simp]
theorem coe_inv_hyperbolicPairUnitsHom (he : Q e = 0) (hef : polar Q e f = 1) (t : Rˣ) :
    ((hyperbolicPairUnitsHom he hef t)⁻¹ : (CliffordAlgebra Q)ˣ) =
      hyperbolicPairScaling Q e f (t⁻¹ : Rˣ) := by
  rw [← map_inv]
  rfl

/-- If `Q e = 0`, then `u(a) e = a (e u(a))`. -/
theorem hyperbolicPairScaling_mul_ι_left (he : Q e = 0) (a : R) :
    hyperbolicPairScaling Q e f a * ι Q e =
      a • (ι Q e * hyperbolicPairScaling Q e f a) := by
  simp only [hyperbolicPairScaling, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc,
    ι_mul_ι_mul_eq_zero he, ι_sq_scalar, he, map_zero, mul_zero, smul_zero, add_zero, zero_add]

/-- If `Q f = 0`, then `a (u(a) f) = f u(a)`. -/
theorem hyperbolicPairScaling_mul_ι_right (hf : Q f = 0) (a : R) :
    a • (hyperbolicPairScaling Q e f a * ι Q f) =
      ι Q f * hyperbolicPairScaling Q e f a := by
  simp only [hyperbolicPairScaling, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc,
    ι_mul_ι_mul_eq_zero hf, ι_sq_scalar, hf, map_zero, mul_zero, smul_zero, add_zero, zero_add]

/-- If `z` is orthogonal to `e` and `f`, then `u(a)` commutes with `z`. -/
theorem commute_hyperbolicPairScaling_ι {z : M} (hez : polar Q e z = 0)
    (hfz : polar Q f z = 0) (a : R) : Commute (hyperbolicPairScaling Q e f a) (ι Q z) := by
  have hez' := isOrtho_polarBilin.mp hez
  have hfz' := isOrtho_polarBilin.mp hfz
  exact ((commute_ι_mul_ι_ι_of_isOrtho hez' hfz').smul_left a).add_left
    (commute_ι_mul_ι_ι_of_isOrtho hfz' hez')

/-- For a hyperbolic pair, `u(t) e u(t)⁻¹ = t e`. -/
theorem hyperbolicPairUnitsHom_mul_ι_left_mul_inv (he : Q e = 0) (hef : polar Q e f = 1)
    (t : Rˣ) :
    ↑(hyperbolicPairUnitsHom he hef t) * ι Q e * ↑(hyperbolicPairUnitsHom he hef t)⁻¹ =
      (t : R) • ι Q e := by
  rw [coe_hyperbolicPairUnitsHom, hyperbolicPairScaling_mul_ι_left he, smul_mul_assoc, mul_assoc,
    ← coe_hyperbolicPairUnitsHom he hef, Units.mul_inv, mul_one]

/-- For a hyperbolic pair, `u(t) f u(t)⁻¹ = t⁻¹ f`. -/
theorem hyperbolicPairUnitsHom_mul_ι_right_mul_inv (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (t : Rˣ) :
    ↑(hyperbolicPairUnitsHom he hef t) * ι Q f * ↑(hyperbolicPairUnitsHom he hef t)⁻¹ =
      ((t⁻¹ : Rˣ) : R) • ι Q f := by
  have h := congrArg (((t⁻¹ : Rˣ) : R) • ·) (hyperbolicPairScaling_mul_ι_right (e := e) hf t)
  simp only [smul_smul, Units.inv_mul, one_smul] at h
  rw [coe_hyperbolicPairUnitsHom, h, smul_mul_assoc, mul_assoc,
    ← coe_hyperbolicPairUnitsHom he hef, Units.mul_inv, mul_one]

/-- For a hyperbolic pair, `u(t)` commutes with every vector orthogonal to `e` and `f`. -/
theorem hyperbolicPairUnitsHom_mul_ι_mul_inv_of_polar_eq_zero (he : Q e = 0)
    (hef : polar Q e f = 1) (t : Rˣ) {z : M} (hez : polar Q e z = 0) (hfz : polar Q f z = 0) :
    ↑(hyperbolicPairUnitsHom he hef t) * ι Q z * ↑(hyperbolicPairUnitsHom he hef t)⁻¹ =
      ι Q z := by
  rw [coe_hyperbolicPairUnitsHom, (commute_hyperbolicPairScaling_ι hez hfz _).eq, mul_assoc,
    ← coe_hyperbolicPairUnitsHom he hef, Units.mul_inv, mul_one]

/-- The vector action of `u(t)` is the torus `TauCeti.QuadraticMap.hyperbolicPairTorus` of the
hyperbolic pair: it scales `e` by `t`, `f` by `t⁻¹`, and fixes their orthogonal complement. -/
theorem hyperbolicPairUnitsHom_mul_ι_mul_inv (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (t : Rˣ) (x : M) :
    ↑(hyperbolicPairUnitsHom he hef t) * ι Q x * ↑(hyperbolicPairUnitsHom he hef t)⁻¹ =
      ι Q ((TauCeti.QuadraticMap.hyperbolicPairTorus Q he hf hef t : M ≃ₗ[R] M) x) := by
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  set y := x - polar Q x f • e - polar Q x e • f with hy
  have hx : x = y + polar Q x f • e + polar Q x e • f := by rw [hy]; abel
  have hey : polar Q e y = 0 := by
    simp [hy, polar_sub_right, polar_smul_right, polar_self, he, hef, polar_comm Q e x]
  have hfy : polar Q f y = 0 := by
    simp [hy, polar_sub_right, polar_smul_right, polar_self, hf, hfe, polar_comm Q f x]
  have hT : (TauCeti.QuadraticMap.hyperbolicPairTorus Q he hf hef t : M ≃ₗ[R] M) x =
      y + ((t : R) * polar Q x f) • e + (((t⁻¹ : Rˣ) : R) * polar Q x e) • f := by
    rw [TauCeti.QuadraticMap.hyperbolicPairTorus_apply, hy]
    module
  rw [hT]
  conv_lhs => rw [hx]
  simp only [map_add, map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    hyperbolicPairUnitsHom_mul_ι_left_mul_inv, hyperbolicPairUnitsHom_mul_ι_right_mul_inv he hf hef,
    hyperbolicPairUnitsHom_mul_ι_mul_inv_of_polar_eq_zero he hef t hey hfy, smul_smul,
    mul_comm (polar Q x f), mul_comm (polar Q x e)]

/-- The reversal of `u(a) = a e f + f e` is `a f e + e f`. -/
theorem reverse_hyperbolicPairScaling (a : R) :
    reverse (hyperbolicPairScaling Q e f a) = a • (ι Q f * ι Q e) + ι Q e * ι Q f := by
  simp [hyperbolicPairScaling, reverse.map_mul]

/-- For a hyperbolic pair, the Clifford norm of `u(a)` is `τ(u(a)) u(a) = a`. -/
theorem reverse_hyperbolicPairScaling_mul_self (he : Q e = 0) (hef : polar Q e f = 1) (a : R) :
    reverse (hyperbolicPairScaling Q e f a) * hyperbolicPairScaling Q e f a =
      algebraMap R _ a := by
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  obtain ⟨hE, hF, hEF, hFE⟩ := hyperbolic_relations he hef
  rw [reverse_hyperbolicPairScaling, hyperbolicPairScaling]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hE, hF, hEF, hFE, smul_zero,
    add_zero, zero_add]
  rw [add_comm, ← smul_add, ι_mul_ι_add_ι_mul_ι_of_polar_eq_one hfe, Algebra.smul_def, mul_one]

/-- For a hyperbolic pair, the norm `star (u(a)) u(a)` of the Lipschitz-group convention is also
`a`. -/
theorem star_hyperbolicPairScaling_mul_self (he : Q e = 0) (hef : polar Q e f = 1) (a : R) :
    star (hyperbolicPairScaling Q e f a) * hyperbolicPairScaling Q e f a = algebraMap R _ a := by
  rw [star_def, involute_hyperbolicPairScaling, reverse_hyperbolicPairScaling_mul_self he hef]

end Pair

end CliffordAlgebra

namespace TauCeti.QuadraticMap

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `(e i, f i)` is a family of mutually orthogonal hyperbolic pairs: `Q (e i) = Q (f i) = 0`,
`polar Q (e i) (f i) = 1`, and vectors from different pairs are orthogonal. -/
structure IsHyperbolicFamily (Q : QuadraticForm R M) (e f : ι → M) : Prop where
  left_isotropic : ∀ i, Q (e i) = 0
  right_isotropic : ∀ i, Q (f i) = 0
  polar_left_right : ∀ i, _root_.QuadraticMap.polar Q (e i) (f i) = 1
  polar_left_left : Pairwise fun i j => _root_.QuadraticMap.polar Q (e i) (e j) = 0
  polar_left_right_of_ne : Pairwise fun i j => _root_.QuadraticMap.polar Q (e i) (f j) = 0
  polar_right_right : Pairwise fun i j => _root_.QuadraticMap.polar Q (f i) (f j) = 0

end TauCeti.QuadraticMap

namespace CliffordAlgebra

open TauCeti.QuadraticMap (IsHyperbolicFamily)

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M}
  {e f : ι → M}

/-- The elements `u_i(a)` and `u_j(b)` of two different pairs of a hyperbolic family commute. -/
theorem commute_hyperbolicPairScaling_of_ne (h : IsHyperbolicFamily Q e f)
    {i j : ι} (hij : i ≠ j) (a b : R) :
    Commute (hyperbolicPairScaling Q (e i) (f i) a) (hyperbolicPairScaling Q (e j) (f j) b) := by
  have hfe : polar Q (f i) (e j) = 0 := by
    rw [polar_comm]
    exact h.polar_left_right_of_ne hij.symm
  have hcomm (z : M) (h₁ : polar Q (e i) z = 0) (h₂ : polar Q (f i) z = 0) :=
    commute_hyperbolicPairScaling_ι (Q := Q) h₁ h₂ a
  exact (((hcomm _ (h.polar_left_left hij) hfe).mul_right
    (hcomm _ (h.polar_left_right_of_ne hij) (h.polar_right_right hij))).smul_right b).add_right
    ((hcomm _ (h.polar_left_right_of_ne hij) (h.polar_right_right hij)).mul_right
      (hcomm _ (h.polar_left_left hij) hfe))

/-- The units `u_i(s)` and `u_j(t)` of two different pairs of a hyperbolic family commute. -/
theorem pairwise_commute_hyperbolicPairUnitsHom (h : IsHyperbolicFamily Q e f) :
    Pairwise fun i j => ∀ s t : Rˣ,
      Commute (hyperbolicPairUnitsHom (h.left_isotropic i) (h.polar_left_right i) s)
        (hyperbolicPairUnitsHom (h.left_isotropic j) (h.polar_left_right j) t) :=
  fun _ _ hij _ _ => Commute.units_val_iff.mp (commute_hyperbolicPairScaling_of_ne h hij _ _)

variable [Fintype ι]

/-- The torus `(c, a) ↦ c ∏ u_i(a_i)` of a family of mutually orthogonal hyperbolic pairs, as a
homomorphism from `Rˣ × (ι → Rˣ)` to the units of the Clifford algebra. For the standard split
forms this is the split maximal torus of the general spin group, with `c` the central scalars. -/
@[expose] noncomputable def hyperbolicTorus (h : IsHyperbolicFamily Q e f) :
    Rˣ × (ι → Rˣ) →* (CliffordAlgebra Q)ˣ :=
  MonoidHom.noncommCoprod (Units.map (algebraMap R (CliffordAlgebra Q) : R →* _))
    (MonoidHom.noncommPiCoprod (fun i => hyperbolicPairUnitsHom (h.left_isotropic i)
      (h.polar_left_right i))
      (pairwise_commute_hyperbolicPairUnitsHom h))
    fun c _ => Commute.units_val_iff.mp (Algebra.commute_algebraMap_left (c : R) _)

/-- The torus element `c ∏ u_i(a_i)` is `c` times the product of the `u_i(a_i)`. -/
theorem coe_hyperbolicTorus (h : IsHyperbolicFamily Q e f) (c : Rˣ) (a : ι → Rˣ) :
    (hyperbolicTorus h (c, a) : CliffordAlgebra Q) =
      algebraMap R _ c * Finset.univ.noncommProd
        (fun i => hyperbolicPairScaling Q (e i) (f i) (a i))
        (fun _ _ _ _ hij => commute_hyperbolicPairScaling_of_ne h hij _ _) := by
  simp only [hyperbolicTorus, MonoidHom.noncommCoprod_apply, Units.val_mul, Units.coe_map,
    MonoidHom.coe_ofClass]
  congr 1
  exact Finset.map_noncommProd _ _ _ (Units.coeHom (CliffordAlgebra Q))

/-- On a single coordinate, the torus is `c u_i(a)`. -/
theorem coe_hyperbolicTorus_mulSingle [DecidableEq ι] (h : IsHyperbolicFamily Q e f) (c : Rˣ)
    (i : ι) (a : Rˣ) :
    (hyperbolicTorus h (c, Pi.mulSingle i a) : CliffordAlgebra Q) =
      algebraMap R _ c * hyperbolicPairScaling Q (e i) (f i) a := by
  rw [hyperbolicTorus, MonoidHom.noncommCoprod_apply, Units.val_mul,
    MonoidHom.noncommPiCoprod_mulSingle]
  rfl

/-- The pairs `(x, r)` with `τ(x) x = r` form a submonoid of `C(Q) × R`. -/
private def reverseNormSubmonoid (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q × R) where
  carrier := {p | reverse p.1 * p.1 = algebraMap R _ p.2}
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, reverse.map_mul, map_mul] at *
    rw [mul_assoc, ← mul_assoc (reverse p.1), hp, Algebra.left_comm, hq, ← map_mul]
  one_mem' := by simp

/-- The Clifford norm of the torus element `c ∏ u_i(a_i)` is `τ(x) x = c² ∏ a_i`. -/
theorem reverse_hyperbolicTorus_mul_self (h : IsHyperbolicFamily Q e f) (c : Rˣ)
    (a : ι → Rˣ) :
    reverse (hyperbolicTorus h (c, a) : CliffordAlgebra Q) * hyperbolicTorus h (c, a) =
      algebraMap R _ ((c : R) ^ 2 * ∏ i, (a i : R)) := by
  have hcomm : (↑(Finset.univ : Finset ι) : Set ι).Pairwise fun i j =>
      Commute ((hyperbolicPairScaling Q (e i) (f i) (a i), (a i : R)) : CliffordAlgebra Q × R)
        (hyperbolicPairScaling Q (e j) (f j) (a j), (a j : R)) :=
    fun i _ j _ hij => Prod.ext (commute_hyperbolicPairScaling_of_ne h hij _ _).eq (mul_comm _ _)
  have hmem := Finset.noncommProd_induction Finset.univ _ hcomm
    (· ∈ reverseNormSubmonoid Q) (fun _ _ => mul_mem) (one_mem _) fun i _ =>
      reverse_hyperbolicPairScaling_mul_self (h.left_isotropic i) (h.polar_left_right i) (a i)
  have h1 := Finset.map_noncommProd _ _ hcomm (MonoidHom.fst (CliffordAlgebra Q) R)
  have h2 := Finset.map_noncommProd _ _ hcomm (MonoidHom.snd (CliffordAlgebra Q) R)
  simp only [MonoidHom.coe_fst, MonoidHom.coe_snd, Finset.noncommProd_eq_prod] at h1 h2
  change reverse _ * _ = algebraMap R _ _ at hmem
  rw [h1, h2] at hmem
  rw [coe_hyperbolicTorus, reverse.map_mul, reverse.commutes, mul_assoc, Algebra.left_comm,
    Algebra.left_comm, hmem, ← map_mul, ← map_mul, ← mul_assoc, ← _root_.sq]

/-- The coroot check of ReductiveGroups §9B.7 for an odd split form: `s ↦ s⁻¹ u_i(s²)` has
Clifford norm one, so it lands in the spin group. -/
theorem reverse_hyperbolicTorus_inv_mulSingle_sq_mul_self [DecidableEq ι]
    (h : IsHyperbolicFamily Q e f) (i : ι) (s : Rˣ) :
    reverse (hyperbolicTorus h (s⁻¹, Pi.mulSingle i (s ^ 2)) : CliffordAlgebra Q) *
      hyperbolicTorus h (s⁻¹, Pi.mulSingle i (s ^ 2)) = 1 := by
  rw [reverse_hyperbolicTorus_mul_self, Finset.prod_eq_single i (fun j _ hj => by
    simp [Pi.mulSingle_eq_of_ne hj]) (by simp), Pi.mulSingle_eq_same,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow,
    Units.val_one, map_one]

end CliffordAlgebra

namespace TauCeti

open TauCeti.QuadraticMap (IsHyperbolicFamily)

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The coordinate hyperbolic pairs `e_i = (0, δ_i)`, `f_i = (δ_i^*, 0)` of the standard split
even form `(φ, x) ↦ φ x`. -/
theorem isHyperbolicFamily_splitEvenForm :
    IsHyperbolicFamily (splitEvenForm K n) (fun i => (0, Pi.single i 1))
      (fun i => (LinearMap.proj i, 0)) where
  left_isotropic _ := by simp
  right_isotropic _ := by simp
  polar_left_right _ := by simp
  polar_left_left _ _ _ := by simp
  polar_left_right_of_ne _ _ hij := by simp [Pi.single_eq_of_ne' hij]
  polar_right_right _ _ _ := by simp

/-- The coordinate hyperbolic pairs `e_i = ((0, δ_i), 0)`, `f_i = ((δ_i^*, 0), 0)` of the
standard split odd form `((φ, x), z) ↦ φ x + z²`. -/
theorem isHyperbolicFamily_splitOddForm :
    IsHyperbolicFamily (splitOddForm K n) (fun i => ((0, Pi.single i 1), 0))
      (fun i => ((LinearMap.proj i, 0), 0)) where
  left_isotropic _ := by simp
  right_isotropic _ := by simp
  polar_left_right _ := by simp
  polar_left_left _ _ _ := by simp
  polar_left_right_of_ne _ _ hij := by simp [Pi.single_eq_of_ne' hij]
  polar_right_right _ _ _ := by simp

end TauCeti
