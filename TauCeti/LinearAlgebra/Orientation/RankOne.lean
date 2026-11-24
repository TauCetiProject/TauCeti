/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Alternating.Basic
public import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.LinearAlgebra.Ray

/-!
# Orientations of one-dimensional modules

On a strict ordered commutative semiring `R` with `[Unique ι]`, composing
`LinearMap.ringLmapEquivSelf` with `AlternatingMap.ofSubsingletonₗ` identifies `Module.Ray R R` with
`Orientation R R ι` (`Orientation.ringRayEquiv`), sending the ray of `1` to the orientation of the
singleton basis of `R` (`Orientation.ringRayEquiv_rayOfNeZero_one`).

Over a linearly ordered field `R`, any one-dimensional vector space `M` (`finrank R M = 1`) carries
a canonical equivalence `Orientation.equivRay : Orientation R M ι ≃ Module.Ray R M` pairing a
nonzero form `ω` with a nonzero vector `v` iff `0 < ω (fun _ ↦ v)`
(`Orientation.equivRay_rayOfNeZero_eq_iff`). It commutes with negation, unit scaling, reindexing,
and linear equivalences (`Orientation.equivRay_map`, `Orientation.map_equivRay_symm`), sends
`b.orientation` of a singleton basis `b` to the ray of `b default`
(`Orientation.equivRay_basis_orientation`), and yields the rank-one ray dichotomy
`Module.Ray.eq_or_eq_neg_of_finrank_eq_one`.
-/

public section

noncomputable section

open Module

namespace Orientation

section Semiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  (ι : Type*) [Unique ι]

/-- On the ground semiring `R`, rays in `R` are canonically equivalent to `ι`-indexed orientations
of `R` when `ι` has a unique element, by sending a scalar `c` to `w ↦ w default * c`. -/
def ringRayEquiv : Module.Ray R R ≃ Orientation R R ι :=
  Module.Ray.map <|
    (LinearMap.ringLmapEquivSelf R R R).symm.trans (AlternatingMap.ofSubsingletonₗ R R R R default)

theorem ringRayEquiv_def : ringRayEquiv (R := R) ι = Module.Ray.map
    ((LinearMap.ringLmapEquivSelf R R R).symm.trans
      (AlternatingMap.ofSubsingletonₗ R R R R default)) := (rfl)

-- Keep for explicit rewriting: `@[simp]` unfolds the LHS of `ringRayEquiv_rayOfNeZero_one`.
theorem ringRayEquiv_apply {ι : Type*} [Unique ι] (c : R) (hc : c ≠ 0) :
    ringRayEquiv ι (rayOfNeZero R c hc) = rayOfNeZero R
      (AlternatingMap.ofSubsingleton R R R (default : ι) (LinearMap.smulRight (1 : R →ₗ[R] R) c))
      (by rw [Ne, ← AlternatingMap.apply_const_one_eq_zero]; simpa using hc) := by
  rw [ringRayEquiv_def, Module.Ray.map_apply]; simp

@[simp]
theorem ringRayEquiv_symm_apply {ι : Type*} [Unique ι] (ω : R [⋀^ι]→ₗ[R] R) (hω : ω ≠ 0) :
    (ringRayEquiv (R := R) ι).symm (rayOfNeZero R ω hω) =
      rayOfNeZero R (ω fun _ ↦ 1) (AlternatingMap.apply_const_one_ne_zero hω) := by
  rw [ringRayEquiv_def, Module.Ray.map_symm, Module.Ray.map_apply]; congr 1; simp

@[simp]
theorem ringRayEquiv_units_smul {ι : Type*} [Unique ι] (u : Rˣ) (r : Module.Ray R R) :
    ringRayEquiv ι (u • r) = u • ringRayEquiv ι r := by
  rw [ringRayEquiv_def, Module.Ray.map_units_smul]

@[simp]
theorem ringRayEquiv_symm_units_smul {ι : Type*} [Unique ι] (u : Rˣ) (o : Orientation R R ι) :
    (ringRayEquiv ι).symm (u • o) = u • (ringRayEquiv ι).symm o := by
  rw [ringRayEquiv_def, Module.Ray.map_symm, Module.Ray.map_units_smul]

end Semiring

section Ring

variable {R ι : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [Unique ι]

@[simp]
theorem ringRayEquiv_neg (r : Module.Ray R R) : ringRayEquiv ι (-r) = -ringRayEquiv ι r := by
  rw [ringRayEquiv_def, Module.Ray.map_neg]

@[simp]
theorem ringRayEquiv_symm_neg (o : Orientation R R ι) :
    (ringRayEquiv ι).symm (-o) = -(ringRayEquiv ι).symm o := by
  rw [ringRayEquiv_def, Module.Ray.map_symm, Module.Ray.map_neg]

/-- The ray of `1 : R` corresponds under `Orientation.ringRayEquiv` to the orientation of the
singleton basis of `R`. -/
@[simp]
theorem ringRayEquiv_rayOfNeZero_one [Fintype ι] [DecidableEq ι] :
    ringRayEquiv ι (rayOfNeZero R (1 : R) one_ne_zero) = (Basis.singleton ι R).orientation := by
  apply (ringRayEquiv ι).symm.injective
  have h1 : (fun _ : ι ↦ (1 : R)) = ⇑(Basis.singleton ι R) :=
    funext fun i ↦ (Basis.singleton_apply ι R i).symm
  rw [Equiv.symm_apply_apply, Basis.orientation, ringRayEquiv_symm_apply]
  congr 1
  rw [h1, Basis.det_self]

end Ring

section Field

variable {R M N ι ι' : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Unique ι]

/-- The canonical equivalence between `ι`-indexed orientations of a one-dimensional vector space `M`
and rays in `M` when `[Unique ι]`, pairing a nonzero form `ω` with a nonzero vector `v` iff
`0 < ω (fun _ ↦ v)` (`Orientation.equivRay_rayOfNeZero_eq_iff`). -/
def equivRay (hM : finrank R M = 1) : Orientation R M ι ≃ Module.Ray R M :=
  haveI : FiniteDimensional R M := Module.finite_of_finrank_eq_succ hM
  let e : M ≃ₗ[R] R := LinearEquiv.ofFinrankEq M R (hM.trans (Module.finrank_self R).symm)
  (Orientation.map ι e).trans ((ringRayEquiv ι).symm.trans (Module.Ray.map e.symm))

theorem equivRay_def (hM : finrank R M = 1) :
    haveI : FiniteDimensional R M := Module.finite_of_finrank_eq_succ hM
    let e : M ≃ₗ[R] R := LinearEquiv.ofFinrankEq M R (hM.trans (Module.finrank_self R).symm)
    equivRay (ι := ι) hM =
      (Orientation.map ι e).trans ((ringRayEquiv ι).symm.trans (Module.Ray.map e.symm)) :=
  (rfl)

/-- **Pairing characterization of `Orientation.equivRay`.** The orientation of a nonzero alternating
form `ω` corresponds to the ray of a nonzero vector `v` iff `0 < ω (fun _ ↦ v)`. -/
theorem equivRay_rayOfNeZero_eq_iff (hM : finrank R M = 1) {ω : M [⋀^ι]→ₗ[R] R} (hω : ω ≠ 0)
    {v : M} (hv : v ≠ 0) :
    equivRay hM (rayOfNeZero R ω hω) = rayOfNeZero R v hv ↔ 0 < ω (fun _ ↦ v) := by
  have : FiniteDimensional R M := Module.finite_of_finrank_eq_succ hM
  let e : M ≃ₗ[R] R := LinearEquiv.ofFinrankEq M R (hM.trans (Module.finrank_self R).symm)
  let a : R := ω (fun _ ↦ e.symm 1)
  have hωe : (ω.compLinearMap e.symm.toLinearMap) (fun _ ↦ (1 : R)) = a :=
    AlternatingMap.compLinearMap_apply ω e.symm.toLinearMap (fun _ ↦ (1 : R))
  have ha : a ≠ 0 := hωe ▸ AlternatingMap.apply_const_one_ne_zero
    fun h ↦ hω (by ext u; simpa using congrArg (· (e ∘ u)) h)
  have hb : e v ≠ 0 := e.map_ne_zero_iff.2 hv
  have hφv : ω (fun _ ↦ v) = a * e v := by
    have hv' : v = e v • e.symm 1 := by
      conv_lhs => rw [← e.symm_apply_apply v, ← mul_one (e v), ← smul_eq_mul, map_smul]
    conv_lhs => rw [hv', AlternatingMap.apply_const_smul, smul_eq_mul, mul_comm]
  have ha_div : a = (a / e v) • e v := by rw [smul_eq_mul, div_mul_cancel₀ a hb]
  rw [equivRay_def, Equiv.trans_apply, Equiv.trans_apply, Orientation.map_apply,
    ringRayEquiv_symm_apply, Module.Ray.map_apply, ray_eq_iff, ← SameRay.sameRay_map_iff e,
    LinearEquiv.apply_symm_apply, hωe, hφv]
  conv_lhs => rw [ha_div]
  exact (sameRay_smul_left_iff_of_ne hb (div_ne_zero ha hb)).trans
    (div_pos_iff.trans mul_pos_iff.symm)

theorem equivRay_symm_rayOfNeZero_eq_iff (hM : finrank R M = 1) {v : M} (hv : v ≠ 0)
    {ω : M [⋀^ι]→ₗ[R] R} (hω : ω ≠ 0) :
    (equivRay hM).symm (rayOfNeZero R v hv) = rayOfNeZero R ω hω ↔ 0 < ω (fun _ ↦ v) := by
  rw [Equiv.symm_apply_eq, eq_comm, equivRay_rayOfNeZero_eq_iff]

@[simp]
theorem equivRay_neg (hM : finrank R M = 1) (o : Orientation R M ι) :
    equivRay hM (-o) = -equivRay hM o := by simp [equivRay]

@[simp]
theorem equivRay_symm_neg (hM : finrank R M = 1) (r : Module.Ray R M) :
    (equivRay (ι := ι) hM).symm (-r) = -(equivRay hM).symm r := by simp [equivRay]

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
  simpa using (equivRay_rayOfNeZero_eq_iff hM hω hv).1 hv_eq

@[simp]
theorem map_equivRay_symm (hM : finrank R M = 1) (f : M ≃ₗ[R] N) (r : Module.Ray R M) :
    Orientation.map ι f ((equivRay hM).symm r) =
      (equivRay (f.finrank_eq.symm.trans hM)).symm (Module.Ray.map f r) :=
  (equivRay (ι := ι) (f.finrank_eq.symm.trans hM)).injective <| by
    rw [equivRay_map (hM := hM), Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp]
theorem equivRay_reindex [Unique ι'] (hM : finrank R M = 1) (σ : ι ≃ ι') (o : Orientation R M ι) :
    equivRay hM (Orientation.reindex R M σ o) = equivRay hM o := by
  induction o using Module.Ray.ind with | h ω hω =>
  generalize hv_eq : equivRay hM (rayOfNeZero R ω hω) = r
  induction r using Module.Ray.ind with | h v hv =>
  rw [Orientation.reindex_apply, equivRay_rayOfNeZero_eq_iff]
  exact (equivRay_rayOfNeZero_eq_iff hM hω hv).1 hv_eq

@[simp]
theorem reindex_equivRay_symm [Unique ι'] (hM : finrank R M = 1) (σ : ι ≃ ι')
    (r : Module.Ray R M) :
    Orientation.reindex R M σ ((equivRay hM).symm r) = (equivRay (ι := ι') hM).symm r :=
  (equivRay (ι := ι') hM).injective <| by
    rw [equivRay_reindex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- For a singleton basis `b` of `M`, `Orientation.equivRay` sends `b.orientation` to the ray of
`b default`. -/
@[simp]
theorem equivRay_basis_orientation [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    equivRay (by rw [finrank_eq_card_basis b, Fintype.card_unique]) b.orientation =
      rayOfNeZero R (b default) (b.ne_zero default) := by
  have hb_eq : (fun _ : ι ↦ b default) = ⇑b :=
    funext fun i ↦ congrArg b (Unique.eq_default i).symm
  rw [Basis.orientation, equivRay_rayOfNeZero_eq_iff, hb_eq, b.det_self]
  exact zero_lt_one

/-- On the ground field `R`, `Orientation.equivRay` agrees with `(Orientation.ringRayEquiv ι).symm`.
-/
theorem equivRay_self : equivRay (ι := ι) (Module.finrank_self R) = (ringRayEquiv ι).symm := by
  ext o
  induction o using Module.Ray.ind with | h ω hω =>
  have hω1 : ω (fun _ ↦ ω (fun _ ↦ 1)) = ω (fun _ ↦ 1) * ω (fun _ ↦ 1) := by
    simpa [smul_eq_mul] using AlternatingMap.apply_const_smul (ι := ι) ω (ω fun _ ↦ 1) 1
  rw [ringRayEquiv_symm_apply, equivRay_rayOfNeZero_eq_iff, hω1]
  exact mul_self_pos.2 (AlternatingMap.apply_const_one_ne_zero hω)

end Field

end Orientation

namespace Module.Ray

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M]

/-- In a one-dimensional vector space over a linearly ordered field, any two rays are equal or
negations of each other. -/
theorem eq_or_eq_neg_of_finrank_eq_one (hM : finrank R M = 1) (r₁ r₂ : Module.Ray R M) :
    r₁ = r₂ ∨ r₁ = -r₂ :=
  (Orientation.eq_or_eq_neg_of_card_eq_finrank ((Orientation.equivRay (ι := Fin 1) hM).symm r₁)
    ((Orientation.equivRay (ι := Fin 1) hM).symm r₂) (by simp [hM])).imp
    (fun h₁ ↦ (Orientation.equivRay (ι := Fin 1) hM).symm.injective h₁)
    (fun h₂ ↦ (Orientation.equivRay (ι := Fin 1) hM).symm.injective
      (h₂.trans (Orientation.equivRay_symm_neg hM r₂).symm))

/-- In a one-dimensional space over a linearly ordered field, `r₁ ≠ r₂` iff `r₁ = -r₂`. -/
theorem ne_iff_eq_neg_of_finrank_eq_one (hM : finrank R M = 1) (r₁ r₂ : Module.Ray R M) :
    r₁ ≠ r₂ ↔ r₁ = -r₂ :=
  ⟨fun h ↦ (eq_or_eq_neg_of_finrank_eq_one hM r₁ r₂).resolve_left h,
    fun h ↦ h.symm ▸ (Module.Ray.ne_neg_self r₂).symm⟩

end Module.Ray
