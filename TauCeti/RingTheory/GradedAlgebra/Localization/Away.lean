/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units

/-!
# The grading of a localization away from a homogeneous element

Let `A` be an `R`-algebra graded by an additive group `ι` (typically `ℤ`) through
`𝒜 : ι → Submodule R A`, and let `f ∈ 𝒜 e`. Then `Localization.Away f` is again graded by `ι`:
the fraction `a / f ^ n` with `a` homogeneous has degree `deg a - n • e`. Unlike Mathlib's
`HomogeneousLocalization.Away 𝒜 f`, which only retains the elements of degree zero, this grading
keeps every degree; for instance `1 / f` has degree `-e`, so for `k[t]` with `t` of degree `1` and
`f = t` it is the grading of `k[t, t⁻¹]` with `t⁻¹` in degree `-1`.

Geometrically, a `ℤ`-grading of `A` is an action of the multiplicative group on `Spec A`, and
`f ∈ 𝒜 e` cuts out an invariant open subscheme `D(f)`; the grading constructed here is the induced
action on `D(f) = Spec A_f`.

## Main definitions

* `TauCeti.GradedAlgebra.awayGrading 𝒜 hf`: for `hf : f ∈ 𝒜 e`, the submodules of
  `Localization.Away f` whose degree-`d` member consists of the fractions `a / f ^ n` with
  `a ∈ 𝒜 (d + n • e)`.
* `TauCeti.GradedAlgebra.awayGradedAlgHom 𝒜 hf`: the localization map `A → A_f` as a graded
  algebra homomorphism `𝒜 →ₐᵍ[R] awayGrading 𝒜 hf`.
* `TauCeti.GradedAlgebra.awayGradingZeroEquiv 𝒜 hf`: the degree-zero part of `awayGrading 𝒜 hf`
  is Mathlib's `HomogeneousLocalization.Away 𝒜 f`.
* `TauCeti.GradedAlgebra.awayLift 𝒜 hf φ hφ`: the universal property of `awayGrading`; a graded
  ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` sending `f` to a unit extends to a graded ring homomorphism
  `awayGrading 𝒜 hf →+*ᵍ ℬ`.

## Main statements

* The instance `GradedAlgebra (awayGrading 𝒜 hf)`, and `isInternal_awayGrading`.
* `TauCeti.GradedAlgebra.coe_decompose_mk`: the degree-`d` component of `a / f ^ n` is
  `a_{d + n • e} / f ^ n`.
* `TauCeti.GradedAlgebra.awayLift_mem_iff` and `TauCeti.GradedAlgebra.awayLift_bijective`: an
  injective `awayLift` reflects degrees, and it is bijective when `φ` exhibits `B` as the
  localization of `A` away from `f`. So the grading of any graded ring that is such a
  localization is the transport of `awayGrading 𝒜 hf`; this identifies `awayGrading` with
  gradings of localizations constructed by other means, such as rings of sections of graded
  quasicoherent algebras over basic opens.
-/

public section

open DirectSum

namespace TauCeti.GradedAlgebra

variable {ι A : Type*} [AddCommGroup ι] {f : A} {e : ι}

section Semiring

variable {R : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (𝒜 : ι → Submodule R A)
  (hf : f ∈ 𝒜 e)

section GradedMonoid

variable [SetLike.GradedMonoid 𝒜]

/-- For `f` homogeneous of degree `e`, the degree-`d` part of `Localization.Away f`: the fractions
`a / f ^ n` with `a ∈ 𝒜 (d + n • e)`, so that `a / f ^ n` has degree `deg a - n • e`. -/
def awayGrading (d : ι) : Submodule R (Localization.Away f) where
  carrier := {x | ∃ n : ℕ, ∃ a ∈ 𝒜 (d + n • e), x = Localization.mk a (Submonoid.pow f n)}
  zero_mem' := ⟨0, 0, zero_mem _, Localization.mk_zero _ |>.symm⟩
  add_mem' := by
    rintro _ _ ⟨n, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
    refine ⟨n + m, f ^ n * b + f ^ m * a, add_mem ?_ ?_, ?_⟩
    · convert SetLike.mul_mem_graded (SetLike.pow_mem_graded n hf) hb using 2
      rw [add_smul]
      abel
    · convert SetLike.mul_mem_graded (SetLike.pow_mem_graded m hf) ha using 2
      rw [add_smul]
      abel
    · rw [Localization.add_mk]
      congr 1
      ext
      simp [pow_add]
  smul_mem' := by
    rintro r _ ⟨n, a, ha, rfl⟩
    exact ⟨n, r • a, Submodule.smul_mem _ r ha, Localization.smul_mk r a _⟩

variable {𝒜 hf}

/-- An element of `Localization.Away f` has degree `d` iff it is a fraction `a / f ^ n` with
`a ∈ 𝒜 (d + n • e)`. -/
theorem mem_awayGrading_iff {d : ι} {x : Localization.Away f} :
    x ∈ awayGrading 𝒜 hf d ↔
      ∃ n : ℕ, ∃ a ∈ 𝒜 (d + n • e), x = Localization.mk a (Submonoid.pow f n) :=
  Iff.rfl

/-- The fraction `a / f ^ n` has degree `d` when `a ∈ 𝒜 (d + n • e)`. -/
theorem mk_mem_awayGrading {d : ι} {n : ℕ} {a : A} (ha : a ∈ 𝒜 (d + n • e)) :
    Localization.mk a (Submonoid.pow f n) ∈ awayGrading 𝒜 hf d :=
  ⟨n, a, ha, rfl⟩

/-- The localization map `A → Localization.Away f` preserves degrees. -/
theorem algebraMap_mem_awayGrading {d : ι} {a : A} (ha : a ∈ 𝒜 d) :
    algebraMap A (Localization.Away f) a ∈ awayGrading 𝒜 hf d := by
  refine ⟨0, a, by simpa using ha, ?_⟩
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1
  ext
  simp

/-- The inverse `1 / f` of a homogeneous element `f` of degree `e` has degree `-e`. -/
theorem invSelf_mem_awayGrading : IsLocalization.Away.invSelf f ∈ awayGrading 𝒜 hf (-e) := by
  refine ⟨1, 1, by simpa using SetLike.GradedOne.one_mem (A := 𝒜), ?_⟩
  rw [IsLocalization.Away.invSelf, Localization.mk_eq_mk'_apply]
  congr
  simp

instance : SetLike.GradedMonoid (awayGrading 𝒜 hf) where
  one_mem := by
    refine ⟨0, 1, by simpa using SetLike.GradedOne.one_mem (A := 𝒜), ?_⟩
    rw [← Localization.mk_one]
    congr 1
    ext
    simp
  mul_mem := by
    rintro i j _ _ ⟨n, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
    refine ⟨n + m, a * b, ?_, ?_⟩
    · convert SetLike.mul_mem_graded ha hb using 2
      rw [add_smul]
      abel
    · rw [Localization.mk_mul]
      congr 1
      ext
      simp [pow_add]

end GradedMonoid

section GradedAlgebra

variable [DecidableEq ι] [GradedAlgebra 𝒜]

/-- The localization map restricted to `𝒜 i`, with values in `awayGrading 𝒜 hf i`. -/
private noncomputable def algebraMapGrade (i : ι) : 𝒜 i →+ awayGrading 𝒜 hf i where
  toFun x := ⟨algebraMap A _ x, algebraMap_mem_awayGrading x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The ring homomorphism `A → ⨁ d, awayGrading 𝒜 hf d` sending `a` to `∑ i, aᵢ / 1`. -/
private noncomputable def toDirectSum : A →+* ⨁ d, awayGrading 𝒜 hf d :=
  (toSemiring (fun i ↦ (of (fun d ↦ awayGrading 𝒜 hf d) i).comp (algebraMapGrade 𝒜 hf i))
    (by
      rw [one_def, AddMonoidHom.comp_apply]
      exact congrArg _ (Subtype.ext (by simp [algebraMapGrade])))
    (fun _ _ ↦ by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, of_mul_of]
      exact congrArg _ (Subtype.ext (by simp [algebraMapGrade, SetLike.coe_gMul])))).comp
    (decomposeRingEquiv 𝒜).toRingHom

private theorem toDirectSum_of_mem {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    toDirectSum 𝒜 hf a = of (fun d ↦ awayGrading 𝒜 hf d) i
      ⟨algebraMap A _ a, algebraMap_mem_awayGrading ha⟩ := by
  simp [toDirectSum, decomposeRingEquiv, decompose_of_mem 𝒜 ha, algebraMapGrade]

private theorem coeRingHom_comp_toDirectSum :
    (coeRingHom (awayGrading 𝒜 hf)).comp (toDirectSum 𝒜 hf) = algebraMap A _ := by
  classical
  ext a
  rw [← sum_support_decompose 𝒜 a]
  simp [toDirectSum_of_mem 𝒜 hf (SetLike.coe_mem _)]

private theorem isUnit_toDirectSum : IsUnit (toDirectSum 𝒜 hf f) := by
  refine IsUnit.of_mul_eq_one
    (of (fun d ↦ awayGrading 𝒜 hf d) (-e) ⟨_, invSelf_mem_awayGrading⟩) ?_
  rw [toDirectSum_of_mem 𝒜 hf hf, of_mul_of, one_def]
  -- the coercions of `GMul.mul` and `GOne.one` are `*` and `1` by definition
  -- (`SetLike.coe_gMul`, `SetLike.coe_gOne`), so the values agree by `mul_invSelf`
  exact of_eq_of_gradedMonoid_eq
    (Sigma.subtype_ext (add_neg_cancel e) (IsLocalization.Away.mul_invSelf f))

/-- The inverse of `coeRingHom (awayGrading 𝒜 hf)`, obtained by inverting `f` in
`toDirectSum 𝒜 hf : A →+* ⨁ d, awayGrading 𝒜 hf d`. -/
private noncomputable def decomposeAux : Localization.Away f →+* ⨁ d, awayGrading 𝒜 hf d :=
  IsLocalization.Away.lift f (isUnit_toDirectSum 𝒜 hf)

private theorem coe_decomposeAux (x : Localization.Away f) :
    DirectSum.coeAddMonoidHom (awayGrading 𝒜 hf) (decomposeAux 𝒜 hf x) = x := by
  have : (coeRingHom (awayGrading 𝒜 hf)).comp (decomposeAux 𝒜 hf) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers f) <| by
      rw [RingHom.comp_assoc, decomposeAux, IsLocalization.Away.lift_comp,
        coeRingHom_comp_toDirectSum, RingHom.id_comp]
  exact congr($this x)

private theorem decomposeAux_coe {i : ι} (x : awayGrading 𝒜 hf i) :
    decomposeAux 𝒜 hf x = of (fun d ↦ awayGrading 𝒜 hf d) i x := by
  obtain ⟨n, a, ha, hx⟩ := x.2
  have hxa : (x : Localization.Away f) * algebraMap A _ (f ^ n) = algebraMap A _ a := by
    rw [hx, Localization.mk_eq_mk'_apply]
    exact IsLocalization.mk'_spec (Localization.Away f) a (Submonoid.pow f n)
  have hu : IsUnit (toDirectSum 𝒜 hf (f ^ n)) := by
    rw [map_pow]
    exact (isUnit_toDirectSum 𝒜 hf).pow n
  refine hu.mul_left_inj.mp ?_
  have h1 : decomposeAux 𝒜 hf x * toDirectSum 𝒜 hf (f ^ n) = toDirectSum 𝒜 hf a := by
    rw [decomposeAux,
      ← IsLocalization.Away.lift_eq (S := Localization.Away f) f (isUnit_toDirectSum 𝒜 hf) (f ^ n),
      ← map_mul, hxa, IsLocalization.Away.lift_eq f (isUnit_toDirectSum 𝒜 hf) a]
  rw [h1, toDirectSum_of_mem 𝒜 hf ha, toDirectSum_of_mem 𝒜 hf (SetLike.pow_mem_graded n hf),
    of_mul_of]
  exact congrArg _ (Subtype.ext (by simpa [SetLike.coe_gMul] using hxa.symm))

/-- `Localization.Away f` is the internal direct sum of the submodules `awayGrading 𝒜 hf d`. -/
theorem isInternal_awayGrading : IsInternal (awayGrading 𝒜 hf) := by
  refine ⟨Function.RightInverse.injective (g := decomposeAux 𝒜 hf) fun y ↦ ?_,
    Function.LeftInverse.surjective (coe_decomposeAux 𝒜 hf)⟩
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i x => simpa using decomposeAux_coe 𝒜 hf x
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- `Localization.Away f` is a graded `R`-algebra, with `a / f ^ n` of degree `deg a - n • e`. -/
noncomputable instance : GradedAlgebra (awayGrading 𝒜 hf) :=
  { (inferInstance : SetLike.GradedMonoid (awayGrading 𝒜 hf)),
    (isInternal_awayGrading 𝒜 hf).chooseDecomposition with }

/-- The localization map `A → Localization.Away f` as a homomorphism of graded `R`-algebras from
`𝒜` to `awayGrading 𝒜 hf`. -/
noncomputable def awayGradedAlgHom : 𝒜 →ₐᵍ[R] awayGrading 𝒜 hf where
  toAlgHom := IsScalarTower.toAlgHom R A (Localization.Away f)
  map_mem := algebraMap_mem_awayGrading

@[simp]
theorem coe_awayGradedAlgHom :
    ⇑(awayGradedAlgHom 𝒜 hf) = algebraMap A (Localization.Away f) :=
  (rfl)

/-- The homogeneous components of `a / 1` are the fractions `aᵢ / 1`. -/
@[simp]
theorem coe_decompose_algebraMap (a : A) (d : ι) :
    (decompose (awayGrading 𝒜 hf) (algebraMap A _ a) d : Localization.Away f) =
      algebraMap A _ (decompose 𝒜 a d) := by
  simpa using (map_directSumDecompose 𝒜 (awayGrading 𝒜 hf) (awayGradedAlgHom 𝒜 hf)).symm

/-- The degree-`d` component of `a / f ^ n` is `a_{d + n • e} / f ^ n`. -/
@[simp]
theorem coe_decompose_mk (n : ℕ) (a : A) (d : ι) :
    (decompose (awayGrading 𝒜 hf) (Localization.mk a (Submonoid.pow f n)) d :
        Localization.Away f) =
      Localization.mk (decompose 𝒜 a (d + n • e) : A) (Submonoid.pow f n) := by
  have h1 : Localization.mk 1 (Submonoid.pow f n) ∈ awayGrading 𝒜 hf (-(n • e)) :=
    mk_mem_awayGrading (by simpa using SetLike.GradedOne.one_mem (A := 𝒜))
  have key := coe_decompose_mul_add_of_right_mem (awayGrading 𝒜 hf) (i := d + n • e)
    (a := algebraMap A _ a) h1
  rw [add_neg_cancel_right, coe_decompose_algebraMap] at key
  simpa [← Localization.mk_one_eq_algebraMap, Localization.mk_mul] using key

end GradedAlgebra

section Lift

variable [DecidableEq ι] {B τ : Type*} [CommSemiring B] [SetLike τ B] [AddSubmonoidClass τ B]
  {ℬ : ι → τ} [GradedRing ℬ]

/-- The lift of `g` sends `a / f ^ n` to the element whose product with `g f ^ n` is `g a`. -/
private theorem lift_mk_mul_pow {g : A →+* B} (hg : IsUnit (g f)) (n : ℕ) (a : A) :
    Localization.awayLift g f hg (Localization.mk a (Submonoid.pow f n)) * g f ^ n = g a := by
  rw [Localization.mk_eq_mk'_apply, mul_comm, ← map_pow]
  exact ((IsLocalization.lift_mk'_spec (S := Localization.Away f) _ a _ (Submonoid.pow f n)).mp
    rfl).symm

section GradedMonoid

variable [SetLike.GradedMonoid 𝒜] (φ : 𝒜 →+*ᵍ ℬ) (hφ : IsUnit (φ f))

/-- **Universal property of `awayGrading`.** A graded ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` sending
`f` to a unit extends to `Localization.Away f`, and the extension is graded for `awayGrading 𝒜 hf`:
it sends `a / f ^ n` with `a` of degree `d + n • e` to `φ a * (φ f)⁻ⁿ`, of degree `d`. This is
the graded form of Mathlib's `Localization.awayLift`. -/
noncomputable def awayLift : awayGrading 𝒜 hf →+*ᵍ ℬ where
  toRingHom := Localization.awayLift φ.toRingHom f hφ
  map_mem := by
    rintro d _ ⟨n, a, ha, rfl⟩
    obtain ⟨u, hu⟩ := hφ.pow n
    have hmem : (u : B) ∈ ℬ (n • e) := hu ▸ SetLike.pow_mem_graded n (φ.map_mem hf)
    have h : Localization.awayLift φ.toRingHom f hφ (Localization.mk a (Submonoid.pow f n)) *
        φ f ^ n = φ a :=
      lift_mk_mul_pow (g := φ.toRingHom) hφ n a
    rw [← hu, ← Units.eq_mul_inv_iff_mul_eq] at h
    rw [h]
    simpa using SetLike.mul_mem_graded (φ.map_mem ha) (u.val_inv_mem_graded hmem)

/-- `awayLift` extends `φ` along the localization map. -/
@[simp]
theorem awayLift_algebraMap (a : A) :
    awayLift 𝒜 hf φ hφ (algebraMap A (Localization.Away f) a) = φ a :=
  IsLocalization.Away.lift_eq f hφ a

/-- If `φ` exhibits `B` as the localization of `A` away from `f`, then `awayLift` is bijective. -/
theorem awayLift_bijective (hloc : letI := φ.toRingHom.toAlgebra; IsLocalization.Away f B) :
    Function.Bijective (awayLift 𝒜 hf φ hφ) := by
  let := φ.toRingHom.toAlgebra
  -- `awayLift` agrees with Mathlib's comparison of two localizations away from `f`.
  have h : (awayLift 𝒜 hf φ hφ).toRingHom =
      (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) B : _ →+* B) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) <|
      RingHom.ext fun a ↦ by simp [RingHom.algebraMap_toAlgebra]
  exact (congrArg DFunLike.coe h).symm ▸
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) B).bijective

end GradedMonoid

variable [GradedAlgebra 𝒜] (φ : 𝒜 →+*ᵍ ℬ) (hφ : IsUnit (φ f))

/-- An injective lift `awayLift 𝒜 hf φ hφ` reflects degrees: an element of `Localization.Away f`
has degree `d` for `awayGrading 𝒜 hf` exactly when its image has degree `d` for `ℬ`. So when
`φ` exhibits `B` as the localization of `A` away from `f` (`awayLift_bijective`), `ℬ` is the
transport of `awayGrading 𝒜 hf`. -/
theorem awayLift_mem_iff (hinj : Function.Injective (awayLift 𝒜 hf φ hφ)) {d : ι}
    {x : Localization.Away f} : awayLift 𝒜 hf φ hφ x ∈ ℬ d ↔ x ∈ awayGrading 𝒜 hf d := by
  refine ⟨fun hx ↦ ?_, (awayLift 𝒜 hf φ hφ).map_mem⟩
  induction x using Localization.induction_on with | H x => ?_
  obtain ⟨a, _, n, rfl⟩ := x
  -- Writing `x = a / f ^ n`, the image `φ a` of the numerator has degree `d + n • e`, so `a` may
  -- be replaced by its homogeneous component of that degree.
  have h : awayLift 𝒜 hf φ hφ (Localization.mk a (Submonoid.pow f n)) * φ f ^ n = φ a :=
    lift_mk_mul_pow (g := φ.toRingHom) hφ n a
  have ha : φ a ∈ ℬ (d + n • e) :=
    h ▸ SetLike.mul_mem_graded hx (SetLike.pow_mem_graded n (φ.map_mem hf))
  have hφa : φ (decompose 𝒜 a (d + n • e)) = φ a := by
    rw [φ.map_directSumDecompose, decompose_of_mem_same ℬ ha]
  have hx' : Localization.mk a (Submonoid.pow f n) =
      Localization.mk (decompose 𝒜 a (d + n • e) : A) (Submonoid.pow f n) := by
    refine hinj ((hφ.pow n).mul_left_inj.mp ?_)
    rw [← hφa] at h
    exact h.trans (lift_mk_mul_pow (g := φ.toRingHom) hφ n (decompose 𝒜 a (d + n • e))).symm
  exact hx' ▸ mk_mem_awayGrading (decompose 𝒜 a (d + n • e)).2

end Lift

end Semiring

section HomogeneousLocalization

variable {R : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (hf : f ∈ 𝒜 e)

/-- The elements of degree zero of `awayGrading 𝒜 hf` are the elements of Mathlib's homogeneous
localization `HomogeneousLocalization.Away 𝒜 f`. -/
theorem range_val_eq_awayGrading_zero :
    Set.range (HomogeneousLocalization.val (𝒜 := 𝒜) (x := .powers f)) = awayGrading 𝒜 hf 0 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf y
    rw [HomogeneousLocalization.Away.val_mk]
    exact mk_mem_awayGrading (by simpa using ha)
  · rintro ⟨n, a, ha, rfl⟩
    exact ⟨HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using ha),
      HomogeneousLocalization.Away.val_mk ..⟩

/-- Mathlib's homogeneous localization `HomogeneousLocalization.Away 𝒜 f` is isomorphic, through
`HomogeneousLocalization.val`, to the degree-zero part of `awayGrading 𝒜 hf`. -/
noncomputable def awayGradingZeroEquiv :
    HomogeneousLocalization.Away 𝒜 f ≃+* awayGrading 𝒜 hf 0 :=
  have hmem (y : HomogeneousLocalization.Away 𝒜 f) : y.val ∈ awayGrading 𝒜 hf 0 := by
    rw [← SetLike.mem_coe, ← range_val_eq_awayGrading_zero]
    exact ⟨y, rfl⟩
  RingEquiv.ofBijective
    ({ toFun y := ⟨y.val, hmem y⟩
       map_one' := Subtype.ext HomogeneousLocalization.val_one
       map_mul' _ _ := Subtype.ext (HomogeneousLocalization.val_mul _ _)
       map_zero' := Subtype.ext HomogeneousLocalization.val_zero
       map_add' _ _ := Subtype.ext (HomogeneousLocalization.val_add _ _) } :
      HomogeneousLocalization.Away 𝒜 f →+* awayGrading 𝒜 hf 0)
    ⟨fun _ _ h ↦ HomogeneousLocalization.val_injective _ congr(Subtype.val $h), fun y ↦ by
      obtain ⟨x, hx⟩ : (y : Localization.Away f) ∈ Set.range HomogeneousLocalization.val := by
        rw [range_val_eq_awayGrading_zero 𝒜 hf]
        exact y.2
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem coe_awayGradingZeroEquiv_apply (y : HomogeneousLocalization.Away 𝒜 f) :
    (awayGradingZeroEquiv 𝒜 hf y : Localization.Away f) = y.val :=
  (rfl)

end HomogeneousLocalization

end TauCeti.GradedAlgebra
