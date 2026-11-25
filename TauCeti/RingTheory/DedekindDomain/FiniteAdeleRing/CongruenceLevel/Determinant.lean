/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Determinants of the congruence levels of `GL₂`

For a commutative ring `A` and an ideal `I`, the diagonal matrix `diag(u, 1)` of a unit `u` lies
in `K₁(I) ⊆ K₀(I)` and has determinant `u`, so the determinants of `K₀(I)` and `K₁(I)` fill `Aˣ`.
The determinants of the principal level `ker(GL₂(A) → GL₂(A ⧸ I))` are the units congruent to `1`
modulo `I`: `≤` because the determinant commutes with reduction, `≥` by `diag(u, 1)` again.

Over the finite adeles of a Dedekind domain `R` with fraction field `K`, with `Ô` the integral
adeles, this gives for every ideal `N` of `R`:

* `det K₀(N) = det K₁(N) = Ô^×`, viewed in `𝔸_f^×`;
* `det K(N) = {x ∈ Ô^× : x ≡ 1 mod NÔ}`.

For `R = ℤ` these are the determinants of `K₀(N)`, `K₁(N)` and `K(N)` in `GL₂(ℤ̂)`.

## Main results

* `TauCeti.diagGL_mem_GL2K1`, `TauCeti.det_diagGL_unit_one`: `diag(u, 1) ∈ K₁(I)` with
  determinant `u`.
* `TauCeti.map_det_GL2K1`, `TauCeti.map_det_GL2K0`: the determinants of `K₁(I)` and `K₀(I)` are
  all of `Aˣ`.
* `TauCeti.map_det_ker_map_quotientMk`: the determinants of the principal level are the units
  congruent to `1` modulo `I`.
* `IsDedekindDomain.FiniteAdeleRing.map_det_level1`,
  `IsDedekindDomain.FiniteAdeleRing.map_det_level0`: `det K₁(N) = det K₀(N) = Ô^×`.
* `IsDedekindDomain.FiniteAdeleRing.map_det_principalLevel`:
  `det K(N) = {x ∈ Ô^× : x ≡ 1 mod NÔ}`.
* `IsDedekindDomain.FiniteAdeleRing.integralGL_diagGL_mem_level1`: for `u ∈ Ô^×`, `diag(u, 1)`
  lies in `K₁(N) ⊆ K₀(N)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13,
  p. 57.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The matrix `diag(u, 1)` lies in `K₁(I)`. -/
theorem diagGL_mem_GL2K1 (u : Aˣ) : diagGL ![u, 1] ∈ GL2K1 I := by
  rw [GL2K1.mem_iff]
  simp

/-- The matrix `diag(u, 1)` lies in `K₀(I)`. -/
theorem diagGL_mem_GL2K0 (u : Aˣ) : diagGL ![u, 1] ∈ GL2K0 I :=
  GL2K1.le_GL2K0 I (diagGL_mem_GL2K1 I u)

/-- The matrix `diag(u, 1)` has determinant `u`. -/
theorem det_diagGL_unit_one (u : Aˣ) : GeneralLinearGroup.det (diagGL ![u, 1]) = u := by
  ext
  simp

/-- **The determinants of `K₁(I)` are all of `Aˣ`.** -/
theorem map_det_GL2K1 : (GL2K1 I).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ ⟨_, diagGL_mem_GL2K1 I u, det_diagGL_unit_one u⟩

/-- **The determinants of `K₀(I)` are all of `Aˣ`.** -/
theorem map_det_GL2K0 : (GL2K0 I).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr ((map_det_GL2K1 I).ge.trans (Subgroup.map_mono (GL2K1.le_GL2K0 I)))

/-- **The determinants of the principal level of `GL₂` are the units congruent to `1`**: the
image under `det` of `ker(GL₂(A) → GL₂(A ⧸ I))` is `ker(Aˣ → (A ⧸ I)ˣ)`. -/
theorem map_det_ker_map_quotientMk :
    (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker.map GeneralLinearGroup.det =
      (Units.map (Ideal.Quotient.mk I : A →* A ⧸ I)).ker := by
  refine le_antisymm ?_ fun u hu ↦ ⟨diagGL ![u, 1], ?_, det_diagGL_unit_one u⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [MonoidHom.mem_ker, ← GeneralLinearGroup.map_det, MonoidHom.mem_ker.mp hg, map_one]
  · have hu' : (u : A) - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_one]
      simpa using congrArg Units.val (MonoidHom.mem_ker.mp hu)
    rw [SetLike.mem_coe, GeneralLinearGroup.mem_ker_map_quotientMk_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu']

end TauCeti

namespace IsDedekindDomain.FiniteAdeleRing

open TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The determinant of the image in `GL_n(𝔸_f)` of a matrix of `GL_n(Ô)` is the image in `𝔸_f^×`
of its determinant. -/
theorem det_integralGL {n : ℕ} (g : GL (Fin n) (integralAdeles R K)) :
    GeneralLinearGroup.det (integralGL K n g) =
      Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])
        (GeneralLinearGroup.det g) := by
  have h : (integralGL K n g : Matrix (Fin n) (Fin n) 𝔸ᶠ[R, K]) =
      (g : Matrix (Fin n) (Fin n) (integralAdeles R K)).map (integralAdeles R K).val.toRingHom :=
    Matrix.ext fun i j ↦ integralGL_apply g i j
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply, h]
  exact (RingHom.map_det _ _).symm

/-- The determinant of the image in `GL₂(𝔸_f)` of a subgroup `H ≤ GL₂(Ô)` is the image in
`𝔸_f^×` of the determinant of `H`. -/
theorem map_det_map_integralGL (H : Subgroup (GL (Fin 2) (integralAdeles R K))) :
    (H.map (integralGL K 2)).map GeneralLinearGroup.det =
      (H.map GeneralLinearGroup.det).map
        (Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g ↦ det_integralGL K g

/-- **`det K₁(N) = Ô^×`**: the determinants of `K₁(N)` are the units of `𝔸_f` coming from units
of the integral adeles. -/
theorem map_det_level1 (N : Ideal R) :
    (level1 K N).map GeneralLinearGroup.det =
      (Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])).range := by
  rw [level1_def, map_det_map_integralGL, map_det_GL2K1, ← MonoidHom.range_eq_map]

/-- **`det K₀(N) = Ô^×`**: the determinants of `K₀(N)` are the units of `𝔸_f` coming from units
of the integral adeles. -/
theorem map_det_level0 (N : Ideal R) :
    (level0 K N).map GeneralLinearGroup.det =
      (Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])).range := by
  rw [level0_def, map_det_map_integralGL, map_det_GL2K0, ← MonoidHom.range_eq_map]

/-- **`det K(N) = {x ∈ Ô^× : x ≡ 1 mod NÔ}`**: the determinants of the principal level `K(N)` are
the images in `𝔸_f^×` of the units of the integral adeles congruent to `1` modulo `NÔ`. -/
theorem map_det_principalLevel (N : Ideal R) :
    (principalLevel K N).map GeneralLinearGroup.det =
      (Units.map (Ideal.Quotient.mk (completedIdeal K N) :
          integralAdeles R K →* integralAdeles R K ⧸ completedIdeal K N)).ker.map
        (Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])) := by
  rw [principalLevel_eq_map_ker, map_det_map_integralGL, map_det_ker_map_quotientMk]

variable {K}

/-- For a unit `u` of the integral adeles, `diag(u, 1)` lies in `K₁(N)`. -/
theorem integralGL_diagGL_mem_level1 (N : Ideal R) (u : (integralAdeles R K)ˣ) :
    integralGL K 2 (diagGL ![u, 1]) ∈ level1 K N := by
  rw [level1_def]
  exact Subgroup.mem_map_of_mem _ (diagGL_mem_GL2K1 _ u)

/-- For a unit `u` of the integral adeles, `diag(u, 1)` lies in `K₀(N)`. -/
theorem integralGL_diagGL_mem_level0 (N : Ideal R) (u : (integralAdeles R K)ˣ) :
    integralGL K 2 (diagGL ![u, 1]) ∈ level0 K N :=
  level1_le_level0 K N (integralGL_diagGL_mem_level1 N u)

/-- The determinant of `diag(u, 1)` in `GL₂(𝔸_f)`, for a unit `u` of the integral adeles, is the
image of `u`. -/
theorem det_integralGL_diagGL (u : (integralAdeles R K)ˣ) :
    GeneralLinearGroup.det (integralGL K 2 (diagGL ![u, 1])) =
      Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K]) u := by
  rw [det_integralGL, det_diagGL_unit_one]

end IsDedekindDomain.FiniteAdeleRing
