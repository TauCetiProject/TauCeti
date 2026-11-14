/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.LinearAlgebra.Ray

/-!
# Orientations of one-dimensional modules

For a singleton index type `ι`, alternating maps `M [⋀^ι]→ₗ[R] N` of one vector are canonically
linearly isomorphic to linear maps `M →ₗ[R] N` (`AlternatingMap.ofSubsingletonₗ`). On the ground
semiring `R`, composing with the canonical identification `R ≃ₗ[R] (R →ₗ[R] R)` identifies rays in
`R` with `ι`-indexed orientations of `R` (`Orientation.ringRayEquiv`), carrying the positive ray of
`1` to the orientation of the singleton basis of `R`.

Over a linearly ordered field `R`, any one-dimensional vector space `M` (`finrank R M = 1`) has a
canonical identification `Orientation.equivRay` between `Orientation R M ι` and `Module.Ray R M`
when `[Unique ι]`: the orientation represented by a nonzero alternating form `ω` corresponds to the
ray of a nonzero vector `v` if and only if `0 < ω (fun _ ↦ v)`
(`Orientation.equivRay_rayOfNeZero_eq_iff`). Because this pairing condition makes no reference to a
coordinate isomorphism `M ≃ₗ[R] R`, the equivalence is independent of auxiliary choices, commutes
with negation, unit scaling, reindexing, and transport along any linear equivalence `M ≃ₗ[R] N`
(`Orientation.equivRay_map`), and sends the orientation of a singleton basis `b` to the ray of
`b default` (`Orientation.equivRay_basis_orientation`). Consequently, any two rays in a
one-dimensional space are equal or opposite (`Module.Ray.eq_or_eq_neg_of_finrank_eq_one`).

## Main definitions

* `AlternatingMap.ofSubsingletonₗ`: linear equivalence `(M →ₗ[R] N) ≃ₗ[R] (M [⋀^ι]→ₗ[R] N)` for a
  subsingleton index type `ι` and element `i : ι`.
* `Orientation.ringRayEquiv`: canonical equivalence `Module.Ray R R ≃ Orientation R R ι` for
  `[Unique ι]`.
* `Orientation.equivRay`: canonical equivalence `Orientation R M ι ≃ Module.Ray R M` for
  `[Unique ι]` when `finrank R M = 1`.

## Main results

* `Orientation.equivRay_rayOfNeZero_eq_iff`: `Orientation.equivRay` pairs `ω` and `v` iff
  `0 < ω (fun _ ↦ v)`.
* `Orientation.equivRay_map`, `Orientation.map_equivRay_symm`: naturality under linear
  equivalences `M ≃ₗ[R] N`.
* `Orientation.equivRay_basis_orientation`: compatibility with `Module.Basis.orientation`.
* `Module.Ray.eq_or_eq_neg_of_finrank_eq_one`: any two rays in a one-dimensional space are equal or
  negations.
-/

public section

noncomputable section

open Module

section Alternating

variable (R M N : Type*) {ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Subsingleton ι]

/-- `AlternatingMap.ofSubsingleton` upgraded to a linear equivalence. -/
def AlternatingMap.ofSubsingletonₗ (i : ι) : (M →ₗ[R] N) ≃ₗ[R] (M [⋀^ι]→ₗ[R] N) :=
  { AlternatingMap.ofSubsingleton R M N i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem AlternatingMap.ofSubsingletonₗ_apply (i : ι) (f : M →ₗ[R] N) (v : ι → M) :
    AlternatingMap.ofSubsingletonₗ R M N i f v = f (v i) :=
  (rfl)

@[simp]
theorem AlternatingMap.ofSubsingletonₗ_symm_apply (i : ι) (ω : M [⋀^ι]→ₗ[R] N) (x : M) :
    (AlternatingMap.ofSubsingletonₗ R M N i).symm ω x = ω (fun _ ↦ x) :=
  (rfl)

end Alternating

namespace Orientation

section Semiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  (ι : Type*) [Unique ι]

/-- On the ground semiring `R`, rays in `R` are canonically equivalent to `ι`-indexed orientations
of `R` when `ι` has a unique element, by sending a scalar `c` to `w ↦ w default * c`. -/
def ringRayEquiv : Module.Ray R R ≃ Orientation R R ι :=
  Module.Ray.map <|
    (LinearMap.ringLmapEquivSelf R R R).symm.trans (AlternatingMap.ofSubsingletonₗ R R R default)

omit [PartialOrder R] [IsStrictOrderedRing R] in
/-- A nonzero alternating form of degree one on `R` is nonzero on the constant tuple `1`. -/
theorem eval_const_one_ne_zero {ι : Type*} [Unique ι] {ω : R [⋀^ι]→ₗ[R] R} (hω : ω ≠ 0) :
    ω (fun _ ↦ 1) ≠ 0 := by
  have hsymm : ((LinearMap.ringLmapEquivSelf R R R).symm.trans
      (AlternatingMap.ofSubsingletonₗ R R R (default : ι))).symm ω = ω (fun _ ↦ 1) := by
    simp
  rw [← hsymm]
  exact (((LinearMap.ringLmapEquivSelf R R R).symm.trans
    (AlternatingMap.ofSubsingletonₗ R R R (default : ι))).symm.map_ne_zero_iff).2 hω

@[simp]
theorem ringRayEquiv_symm_apply {ι : Type*} [Unique ι] (ω : R [⋀^ι]→ₗ[R] R) (hω : ω ≠ 0) :
    (ringRayEquiv (R := R) ι).symm (rayOfNeZero R ω hω) =
      rayOfNeZero R (ω fun _ ↦ 1) (eval_const_one_ne_zero hω) := by
  rw [ringRayEquiv, Module.Ray.map_symm, Module.Ray.map_apply]
  congr 1

@[simp]
theorem ringRayEquiv_units_smul {ι : Type*} [Unique ι] (u : Rˣ) (r : Module.Ray R R) :
    ringRayEquiv ι (u • r) = u • ringRayEquiv ι r := by
  rw [ringRayEquiv, Module.Ray.map_units_smul]

@[simp]
theorem ringRayEquiv_symm_units_smul {ι : Type*} [Unique ι] (u : Rˣ) (o : Orientation R R ι) :
    (ringRayEquiv ι).symm (u • o) = u • (ringRayEquiv ι).symm o := by
  rw [ringRayEquiv, Module.Ray.map_symm, Module.Ray.map_units_smul]

end Semiring

section Ring

variable {R ι : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [Unique ι]

@[simp]
theorem ringRayEquiv_neg (r : Module.Ray R R) :
    ringRayEquiv ι (-r) = -ringRayEquiv ι r := by
  rw [ringRayEquiv, Module.Ray.map_neg]

@[simp]
theorem ringRayEquiv_symm_neg (o : Orientation R R ι) :
    (ringRayEquiv ι).symm (-o) = -(ringRayEquiv ι).symm o := by
  rw [ringRayEquiv, Module.Ray.map_symm, Module.Ray.map_neg]

/-- The ray of `1 : R` corresponds under `Orientation.ringRayEquiv` to the orientation of the
singleton basis of `R`. -/
@[simp]
theorem ringRayEquiv_rayOfNeZero_one [Fintype ι] [DecidableEq ι] :
    ringRayEquiv ι (rayOfNeZero R (1 : R) one_ne_zero) = (Basis.singleton ι R).orientation := by
  apply (ringRayEquiv ι).symm.injective
  rw [Equiv.symm_apply_apply, Basis.orientation, ringRayEquiv_symm_apply]
  congr 1
  have hb : (fun _ : ι ↦ (1 : R)) = ⇑(Basis.singleton ι R) :=
    funext fun i ↦ (Basis.singleton_apply ι R i).symm
  rw [hb, Basis.det_self]

end Ring

section Field

variable {R M N ι ι' : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Unique ι]

/-- The canonical equivalence between `ι`-indexed orientations of a one-dimensional vector space `M`
and rays in `M` when `[Unique ι]`. The orientation of a nonzero form `ω` corresponds to the ray of
a nonzero vector `v` precisely when `0 < ω (fun _ ↦ v)`
(`Orientation.equivRay_rayOfNeZero_eq_iff`). -/
def equivRay (hM : finrank R M = 1) : Orientation R M ι ≃ Module.Ray R M :=
  haveI : FiniteDimensional R M := Module.finite_of_finrank_eq_succ hM
  let e : M ≃ₗ[R] R := LinearEquiv.ofFinrankEq M R (hM.trans (Module.finrank_self R).symm)
  (Orientation.map ι e).trans ((ringRayEquiv ι).symm.trans (Module.Ray.map e.symm))

/-- **Pairing characterization of `Orientation.equivRay`.** The orientation of a nonzero alternating
form `ω` corresponds to the ray of a nonzero vector `v` if and only if `ω` is positive on `(v)`. -/
theorem equivRay_rayOfNeZero_eq_iff (hM : finrank R M = 1) {ω : M [⋀^ι]→ₗ[R] R} (hω : ω ≠ 0)
    {v : M} (hv : v ≠ 0) :
    equivRay hM (rayOfNeZero R ω hω) = rayOfNeZero R v hv ↔ 0 < ω (fun _ ↦ v) := by
  have : FiniteDimensional R M := Module.finite_of_finrank_eq_succ hM
  let e : M ≃ₗ[R] R := LinearEquiv.ofFinrankEq M R (hM.trans (Module.finrank_self R).symm)
  let φ : M →ₗ[R] R := (AlternatingMap.ofSubsingletonₗ R M R (default : ι)).symm ω
  let a : R := ω (fun _ ↦ e.symm 1)
  have ha : a ≠ 0 := by
    intro ha0
    refine hω ((AlternatingMap.ofSubsingletonₗ R M R (default : ι)).symm.injective ?_)
    rw [map_zero]
    refine LinearMap.ext (e.symm.surjective.forall.2 fun r ↦ ?_)
    calc φ (e.symm r) = φ (r • e.symm 1) := by rw [← map_smul, smul_eq_mul, mul_one]
    _ = r • a := map_smul φ r (e.symm 1)
    _ = 0 := by rw [ha0, smul_zero]
  have hb : e v ≠ 0 := e.map_ne_zero_iff.2 hv
  have hφv : ω (fun _ ↦ v) = a * e v := by
    have hv' : v = e v • e.symm 1 := by
      conv_lhs => rw [← e.symm_apply_apply v, ← mul_one (e v), ← smul_eq_mul, map_smul]
    calc ω (fun _ ↦ v) = φ v := (AlternatingMap.ofSubsingletonₗ_symm_apply R M R default ω v).symm
    _ = φ (e v • e.symm 1) := congrArg φ hv'
    _ = a * e v := by rw [map_smul, smul_eq_mul, mul_comm]; rfl
  simp only [equivRay, Equiv.trans_apply, Orientation.map_apply, ringRayEquiv_symm_apply,
    Module.Ray.map_apply, ray_eq_iff, AlternatingMap.compLinearMap_apply]
  rw [← SameRay.sameRay_map_iff e, LinearEquiv.apply_symm_apply, hφv]
  have ha_eq : (a / e v) • e v = a := by rw [smul_eq_mul, div_mul_cancel₀ a hb]
  calc SameRay R (ω fun _ ↦ (LinearEquiv.ofFinrankEq M R _).symm 1) (e v)
      ↔ SameRay R ((a / e v) • e v) (e v) := by rw [ha_eq]
  _ ↔ 0 < a / e v := sameRay_smul_left_iff_of_ne hb (div_ne_zero ha hb)
  _ ↔ 0 < a * e v := div_pos_iff.trans mul_pos_iff.symm

/-- Dual form of `Orientation.equivRay_rayOfNeZero_eq_iff` for `(Orientation.equivRay hM).symm`. -/
theorem equivRay_symm_rayOfNeZero_eq_iff (hM : finrank R M = 1) {v : M} (hv : v ≠ 0)
    {ω : M [⋀^ι]→ₗ[R] R} (hω : ω ≠ 0) :
    (equivRay hM).symm (rayOfNeZero R v hv) = rayOfNeZero R ω hω ↔ 0 < ω (fun _ ↦ v) := by
  rw [Equiv.symm_apply_eq, eq_comm, equivRay_rayOfNeZero_eq_iff]

@[simp]
theorem equivRay_neg (hM : finrank R M = 1) (o : Orientation R M ι) :
    equivRay hM (-o) = -equivRay hM o := by
  simp [equivRay]

@[simp]
theorem equivRay_symm_neg (hM : finrank R M = 1) (r : Module.Ray R M) :
    (equivRay (ι := ι) hM).symm (-r) = -(equivRay hM).symm r := by
  simp [equivRay]

@[simp]
theorem equivRay_units_smul (hM : finrank R M = 1) (u : Rˣ) (o : Orientation R M ι) :
    equivRay hM (u • o) = u • equivRay hM o :=
  Module.Ray.units_smul_of_map_neg (equivRay_neg hM) u o

@[simp]
theorem equivRay_symm_units_smul (hM : finrank R M = 1) (u : Rˣ) (r : Module.Ray R M) :
    (equivRay (ι := ι) hM).symm (u • r) = u • (equivRay hM).symm r :=
  Module.Ray.units_smul_of_map_neg (equivRay_symm_neg hM) u r

/-- `Orientation.equivRay` is natural with respect to linear equivalences `M ≃ₗ[R] N`. -/
@[simp]
theorem equivRay_map (hM : finrank R M = 1) (f : M ≃ₗ[R] N) (o : Orientation R M ι) :
    equivRay (f.finrank_eq.symm.trans hM) (Orientation.map ι f o) =
      Module.Ray.map f (equivRay hM o) := by
  induction o using Module.Ray.ind with | h ω hω =>
  generalize hv_eq : equivRay hM (rayOfNeZero R ω hω) = r
  induction r using Module.Ray.ind with | h v hv =>
  rw [Module.Ray.map_apply, Orientation.map_apply, equivRay_rayOfNeZero_eq_iff]
  have hpos : 0 < ω (fun _ ↦ v) := (equivRay_rayOfNeZero_eq_iff hM hω hv).1 hv_eq
  simpa only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hpos

/-- Transporting the orientation associated to a ray along `f : M ≃ₗ[R] N` gives the orientation
associated to the mapped ray. -/
@[simp]
theorem map_equivRay_symm (hM : finrank R M = 1) (f : M ≃ₗ[R] N) (r : Module.Ray R M) :
    Orientation.map ι f ((equivRay hM).symm r) =
      (equivRay (f.finrank_eq.symm.trans hM)).symm (Module.Ray.map f r) := by
  apply (equivRay (ι := ι) (f.finrank_eq.symm.trans hM)).injective
  rw [equivRay_map (hM := hM), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Reindexing between two singleton index types does not change the ray associated to an
orientation. -/
@[simp]
theorem equivRay_reindex [Unique ι'] (hM : finrank R M = 1) (σ : ι ≃ ι')
    (o : Orientation R M ι) :
    equivRay hM (Orientation.reindex R M σ o) = equivRay hM o := by
  induction o using Module.Ray.ind with | h ω hω =>
  generalize hv_eq : equivRay hM (rayOfNeZero R ω hω) = r
  induction r using Module.Ray.ind with | h v hv =>
  rw [Orientation.reindex_apply, equivRay_rayOfNeZero_eq_iff]
  exact (equivRay_rayOfNeZero_eq_iff hM hω hv).1 hv_eq

/-- Reindexing the orientation associated to a ray between singleton index types gives the
orientation associated to the same ray. -/
@[simp]
theorem reindex_equivRay_symm [Unique ι'] (hM : finrank R M = 1) (σ : ι ≃ ι')
    (r : Module.Ray R M) :
    Orientation.reindex R M σ ((equivRay hM).symm r) = (equivRay (ι := ι') hM).symm r := by
  apply (equivRay (ι := ι') hM).injective
  rw [equivRay_reindex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- For a singleton basis `b` of `M`, `Orientation.equivRay` sends `b.orientation` to the ray of
its unique basis vector `b default`. -/
@[simp]
theorem equivRay_basis_orientation [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    equivRay (by rw [finrank_eq_card_basis b, Fintype.card_unique]) b.orientation =
      rayOfNeZero R (b default) (b.ne_zero default) := by
  rw [Basis.orientation, equivRay_rayOfNeZero_eq_iff]
  have hb : (fun _ : ι ↦ b default) = ⇑b := funext fun i ↦ congrArg b (Unique.eq_default i).symm
  rw [hb, b.det_self]
  exact zero_lt_one

/-- On the ground field `R`, `Orientation.equivRay` agrees with `(Orientation.ringRayEquiv ι).symm`.
-/
@[simp]
theorem equivRay_self :
    equivRay (ι := ι) (Module.finrank_self R) = (ringRayEquiv ι).symm := by
  ext o
  induction o using Module.Ray.ind with | h ω hω =>
  rw [ringRayEquiv_symm_apply, equivRay_rayOfNeZero_eq_iff]
  have hω1 : ω (fun _ ↦ (1 : R)) ≠ 0 := eval_const_one_ne_zero hω
  have hmul : ω (fun _ ↦ ω (fun _ ↦ 1)) = ω (fun _ ↦ 1) * ω (fun _ ↦ 1) := by
    let φ : R →ₗ[R] R := (AlternatingMap.ofSubsingletonₗ R R R (default : ι)).symm ω
    calc ω (fun _ ↦ ω (fun _ ↦ 1)) = φ (ω (fun _ ↦ 1)) :=
        (AlternatingMap.ofSubsingletonₗ_symm_apply R R R default ω _).symm
    _ = φ (ω (fun _ ↦ 1) • 1) := by rw [smul_eq_mul, mul_one]
    _ = ω (fun _ ↦ 1) * ω (fun _ ↦ 1) := by rw [map_smul, smul_eq_mul]; rfl
  rw [hmul]
  exact mul_self_pos.2 hω1

end Field

end Orientation

namespace Module.Ray

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M]

/-- In a one-dimensional vector space over a linearly ordered field, any two rays are equal or
negations of each other. -/
theorem eq_or_eq_neg_of_finrank_eq_one (hM : finrank R M = 1) (r₁ r₂ : Module.Ray R M) :
    r₁ = r₂ ∨ r₁ = -r₂ := by
  have h := Orientation.eq_or_eq_neg_of_card_eq_finrank
    ((Orientation.equivRay (ι := Fin 1) hM).symm r₁)
    ((Orientation.equivRay (ι := Fin 1) hM).symm r₂) (by simp [hM])
  exact h.imp (fun h₁ ↦ (Orientation.equivRay (ι := Fin 1) hM).symm.injective h₁) fun h₂ ↦
    (Orientation.equivRay (ι := Fin 1) hM).symm.injective
      (h₂.trans (Orientation.equivRay_symm_neg hM r₂).symm)

/-- In a one-dimensional vector space over a linearly ordered field, a ray differs from another
precisely when it is the opposite ray. -/
theorem ne_iff_eq_neg_of_finrank_eq_one (hM : finrank R M = 1) (r₁ r₂ : Module.Ray R M) :
    r₁ ≠ r₂ ↔ r₁ = -r₂ :=
  ⟨fun h ↦ (eq_or_eq_neg_of_finrank_eq_one hM r₁ r₂).resolve_left h,
    fun h ↦ h.symm ▸ (Module.Ray.ne_neg_self r₂).symm⟩

end Module.Ray
