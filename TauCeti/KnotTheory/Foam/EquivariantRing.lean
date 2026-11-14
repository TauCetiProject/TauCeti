/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.Algebra.Category.GradedModuleCat.HomogeneousBasis
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The equivariant coefficient ring and integral freeness of graded retracts

For `N : ℕ`, the integral `GL(N)`-equivariant cohomology ring of a point is the polynomial ring
`Λ_N = ℤ[e₁, …, e_N]` in `N` elementary symmetric generators, where `e_{i+1} = MvPolynomial.X i`
has internal degree `2(i + 1)`. We formalise this graded ring as `TauCeti.EquivariantRing N`
equipped with `TauCeti.EquivariantRing.grading N`.

Because every variable weight `2(i + 1)` is strictly positive and even:

* `EquivariantRing.grading N d = ⊥` whenever `d < 0` or `Odd d`;
* `EquivariantRing.grading N 0 = 1` is isomorphic as a `ℤ`-algebra and ring to `ℤ`, and therefore
  carries `IsDomain` and `IsPrincipalIdealRing` instances (including in the case `N = 0`).

Applying the graded Nakayama basis-lifting and idempotent-retract theorems from
`TauCeti.Algebra.Category.GradedModuleCat.HomogeneousBasis` to `EquivariantRing.grading N` yields
integral freeness of graded retracts of finite shifted sums of `Λ_N`:

* in `GradedModuleCat (EquivariantRing.grading N)`, every idempotent endomorphism of a finite
  biproduct of shifted copies of `Λ_N` splits through a finite biproduct of shifted copies of `Λ_N`;
* on concrete column vectors `Fin m → EquivariantRing N` with source shifts `s : Fin m → ℤ`, every
  degree-zero idempotent `p` factors as `p = ι ∘ π` with `π ∘ ι = id` through homogeneous matrices
  `ι` and `π` for target shifts `d : Fin n → ℤ`, equipping `LinearMap.range p` with a finite
  homogeneous `EquivariantRing N`-basis (`exists_homogeneous_basis_range_idempotent`).

In planar `𝔤𝔩(N)` foam evaluation, applying this splitting to the idempotent `u ∘ v` on the state
module `P_W` decomposes any closed or open planar web `W` into a finite direct sum of shifted empty
webs over `Λ_N`.

## Main definitions

* `TauCeti.EquivariantRing`: the polynomial ring `MvPolynomial (Fin N) ℤ`.
* `TauCeti.EquivariantRing.weight`: the weight assignment `i ↦ 2 * (i + 1)`.
* `TauCeti.EquivariantRing.grading`: the `ℤ`-grading of `EquivariantRing N` with `X i` in degree
  `2(i + 1)`.
* `TauCeti.EquivariantRing.gradingZeroAlgEquiv`, `TauCeti.EquivariantRing.gradingZeroRingEquiv`:
  the canonical identifications `EquivariantRing.grading N 0 ≃ₐ[ℤ] ℤ` and
  `EquivariantRing.grading N 0 ≃+* ℤ`.

## Main results

* `TauCeti.EquivariantRing.grading_eq_bot_of_lt_zero`,
  `TauCeti.EquivariantRing.grading_eq_bot_of_odd`: `Λ_N` is concentrated in non-negative even
  degrees.
* `TauCeti.EquivariantRing.exists_biproduct_shift_retract_of_idempotent`: categorical biproduct
  retract splitting of idempotents on finite sums of shifts of `Λ_N`.
* `TauCeti.exists_homogeneous_retract_of_idempotent`: explicit homogeneous matrix factorisation
  `p = ι ∘ π`, `π ∘ ι = id` and homogeneous basis of `LinearMap.range p`.
* `TauCeti.exists_homogeneous_basis_range_idempotent`: every degree-zero idempotent on a finite
  shifted sum of copies of `EquivariantRing N` has a finite homogeneous basis of its image.
* `TauCeti.EquivariantRing.eq_one_and_deg_eq_of_span_singleton`: rank and generator degree
  uniqueness for homogeneous submodules spanned by a single non-zero homogeneous vector over
  `EquivariantRing N`.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov--Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), Section 3.3, Theorem 3.30 and Lemma 3.31.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

/-- The integral `GL(N)`-equivariant coefficient ring `Λ_N = ℤ[e₁, …, e_N]`, realised as the
multivariate polynomial ring `MvPolynomial (Fin N) ℤ` in which `MvPolynomial.X i` represents the
`(i + 1)`-st elementary symmetric generator `e_{i+1}`. -/
abbrev EquivariantRing (N : ℕ) : Type := MvPolynomial (Fin N) ℤ

namespace EquivariantRing

/-- Weight of the `i`-th generator `e_{i+1} = MvPolynomial.X i` in `EquivariantRing N`, namely
`2 * (i + 1)`. -/
@[expose]
def weight (N : ℕ) (i : Fin N) : ℤ :=
  2 * ((i : ℕ) + 1 : ℤ)

theorem weight_pos (N : ℕ) (i : Fin N) : 0 < weight N i := by
  simp only [weight]
  omega

theorem even_weight (N : ℕ) (i : Fin N) : Even (weight N i) :=
  ⟨(i : ℕ) + 1, by simp only [weight]; ring⟩

/-- The integral grading on `EquivariantRing N` placing `MvPolynomial.X i` (`e_{i+1}`) in degree
`2 * (i + 1)`. -/
@[expose]
def grading (N : ℕ) : ℤ → Submodule ℤ (EquivariantRing N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N)

instance instGradedAlgebraGrading (N : ℕ) : GradedAlgebra (grading N) :=
  MvPolynomial.weightedGradedAlgebra ℤ (weight N)

@[simp]
theorem X_mem_grading (N : ℕ) (i : Fin N) :
    (MvPolynomial.X i : EquivariantRing N) ∈ grading N (2 * ((i : ℕ) + 1 : ℤ)) :=
  MvPolynomial.isWeightedHomogeneous_X ℤ (weight N) i

theorem C_mem_grading_zero (N : ℕ) (c : ℤ) :
    (MvPolynomial.C c : EquivariantRing N) ∈ grading N 0 :=
  MvPolynomial.isWeightedHomogeneous_C (weight N) c

/-- `EquivariantRing N` vanishes in all negative degrees. -/
theorem grading_eq_bot_of_lt_zero (N : ℕ) (d : ℤ) (hd : d < 0) :
    grading N d = ⊥ :=
  MvPolynomial.weightedHomogeneousSubmodule_eq_bot_of_lt_zero
    (fun i ↦ (weight_pos N i).le) hd

/-- `EquivariantRing N` vanishes in all odd degrees. -/
theorem grading_eq_bot_of_odd (N : ℕ) {d : ℤ} (hd : Odd d) :
    grading N d = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro φ hφ
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hdeg : Finsupp.weight (weight N) m = d := hφ hm
  obtain ⟨b, rfl⟩ := hd
  have hdvd : (2 : ℤ) ∣ 2 * b + 1 := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.dvd_sum fun i _ ↦
      ⟨(m i : ℤ) * ((i : ℕ) + 1), by simp only [weight, nsmul_eq_mul]; ring⟩
  obtain ⟨a, ha⟩ := hdvd
  omega

/-- The degree-zero piece of `EquivariantRing N` is the image of `ℤ`. -/
theorem grading_zero_eq_one (N : ℕ) : grading N 0 = 1 :=
  MvPolynomial.weightedHomogeneousSubmodule_zero_of_pos (weight_pos N)

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
/-- The canonical `ℤ`-algebra isomorphism `EquivariantRing.grading N 0 ≃ₐ[ℤ] ℤ` given by taking
the constant coefficient. -/
def gradingZeroAlgEquiv (N : ℕ) : grading N 0 ≃ₐ[ℤ] ℤ :=
  MvPolynomial.weightedGradeZeroAlgEquiv (weight_pos N)

/-- The canonical ring isomorphism `EquivariantRing.grading N 0 ≃+* ℤ`. -/
def gradingZeroRingEquiv (N : ℕ) : grading N 0 ≃+* ℤ :=
  (gradingZeroAlgEquiv N).toRingEquiv

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
@[simp]
theorem gradingZeroAlgEquiv_apply (N : ℕ) (x : grading N 0) :
    gradingZeroAlgEquiv N x = MvPolynomial.constantCoeff (x : EquivariantRing N) :=
  MvPolynomial.weightedGradeZeroAlgEquiv_apply (weight_pos N) x

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
theorem coe_gradingZeroAlgEquiv_symm_apply (N : ℕ) (c : ℤ) :
    ((gradingZeroAlgEquiv N).symm c : EquivariantRing N) = MvPolynomial.C c :=
  MvPolynomial.coe_weightedGradeZeroAlgEquiv_symm_apply (weight_pos N) c

instance instIsDomainGradingZero (N : ℕ) : IsDomain (grading N 0) :=
  (gradingZeroRingEquiv N).toMulEquiv.isDomain ℤ

instance instIsPrincipalIdealRingGradingZero (N : ℕ) : IsPrincipalIdealRing (grading N 0) :=
  IsPrincipalIdealRing.of_surjective
    (gradingZeroRingEquiv N).symm.toRingHom
    (gradingZeroRingEquiv N).symm.surjective

/-- **Biproduct retract splitting over `Λ_N`.** In `GradedModuleCat (EquivariantRing.grading N)`,
every idempotent endomorphism of a finite biproduct of shifted copies of `Λ_N` splits through a
finite biproduct of shifted copies of `Λ_N` via morphisms `ι` and `π` satisfying `π ≫ ι = e` and
`ι ≫ π = 𝟙 _`. -/
theorem exists_biproduct_shift_retract_of_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (e : Limits.biproduct (fun j : Fin m ↦
        (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (s j)) ⟶
      Limits.biproduct (fun j : Fin m ↦
        (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (s j)))
    (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : Limits.biproduct (fun i : Fin n ↦
          (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (d i)) ⟶
        Limits.biproduct (fun j : Fin m ↦
          (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (s j)))
      (π : Limits.biproduct (fun j : Fin m ↦
          (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (s j)) ⟶
        Limits.biproduct (fun i : Fin n ↦
          (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (d i))),
      π ≫ ι = e ∧
        ι ≫ π = 𝟙 (Limits.biproduct fun i : Fin n ↦
          (GradedModuleCat.regular (𝒜 := grading N)).shiftObj (d i)) := by
  let isoS := GradedModuleCat.freeIsoBiproduct (𝒜 := grading N) s
  let eFree : GradedModuleCat.free (grading N) s ⟶ GradedModuleCat.free (grading N) s :=
    isoS.hom ≫ e ≫ isoS.inv
  have heFree : eFree ≫ eFree = eFree := by
    simp only [eFree, Category.assoc]
    rw [← Category.assoc isoS.inv, isoS.inv_hom_id, Category.id_comp, ← Category.assoc e, he]
  obtain ⟨n, d, ιF, πF, -, hπι, hιπ, -⟩ :=
    GradedModuleCat.exists_free_retract_of_idempotent (grading_eq_bot_of_lt_zero N) eFree heFree
  let isoD := GradedModuleCat.freeIsoBiproduct (𝒜 := grading N) d
  refine ⟨n, d, isoD.inv ≫ ιF ≫ isoS.hom, isoS.inv ≫ πF ≫ isoD.hom, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [← Category.assoc isoD.hom, isoD.hom_inv_id, Category.id_comp, ← Category.assoc πF, hπι]
    simp only [eFree, Category.assoc, isoS.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, isoS.inv_hom_id, Category.id_comp]
  · simp only [Category.assoc]
    rw [← Category.assoc isoS.hom, isoS.hom_inv_id, Category.id_comp, ← Category.assoc ιF, hιπ,
      Category.id_comp, isoD.inv_hom_id]

end EquivariantRing

/-- Linear equivalence `P ≃ₗ[R] LinearMap.range p` induced by a linear splitting `ι.comp π = p`,
`π.comp ι = id`. -/
private def retractLinearEquivRange {R P M : Type*} [Semiring R] [AddCommMonoid P]
    [AddCommMonoid M] [Module R P] [Module R M] {p : M →ₗ[R] M}
    (ι : P →ₗ[R] M) (π : M →ₗ[R] P) (hιπ : ι.comp π = p) (hπι : π.comp ι = LinearMap.id) :
    P ≃ₗ[R] LinearMap.range p :=
  have hmem : ∀ w : P, ι w ∈ LinearMap.range p := fun w ↦
    ⟨ι w, by
      calc
        p (ι w) = ι (π (ι w)) := (LinearMap.congr_fun hιπ (ι w)).symm
        _ = ι w := congrArg ι (LinearMap.congr_fun hπι w)⟩
  LinearEquiv.ofLinearMap
    (ι.codRestrict (LinearMap.range p) hmem)
    (π.comp (LinearMap.range p).subtype)
    (LinearMap.ext fun ⟨_, v, rfl⟩ ↦ Subtype.ext <| by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
        Submodule.subtype_apply, LinearMap.id_coe, id_eq]
      calc
        ι (π (p v)) = ι (π (ι (π v))) :=
          (congrArg (fun x ↦ ι (π x)) (LinearMap.congr_fun hιπ v)).symm
        _ = ι (π v) := congrArg ι (LinearMap.congr_fun hπι (π v))
        _ = p v := LinearMap.congr_fun hιπ v)
    (LinearMap.ext fun w ↦ LinearMap.congr_fun hπι w)

@[simp]
private theorem coe_retractLinearEquivRange_apply {R P M : Type*} [Semiring R] [AddCommMonoid P]
    [AddCommMonoid M] [Module R P] [Module R M] {p : M →ₗ[R] M}
    (ι : P →ₗ[R] M) (π : M →ₗ[R] P) (hιπ : ι.comp π = p) (hπι : π.comp ι = LinearMap.id)
    (w : P) :
    (retractLinearEquivRange ι π hιπ hπι w : M) = ι w :=
  rfl

/-- Transport a graded morphism between finite graded free modules over `EquivariantRing N` to an
`EquivariantRing N`-linear map between `Fin`-indexed function modules. -/
private def fromFreeHom {N a b : ℕ} {sa : Fin a → ℤ} {sb : Fin b → ℤ}
    (f : GradedModuleCat.free (EquivariantRing.grading N) sa ⟶
      GradedModuleCat.free (EquivariantRing.grading N) sb) :
    (Fin a → EquivariantRing N) →ₗ[EquivariantRing N] (Fin b → EquivariantRing N) :=
  let eA := DirectSum.linearEquivFunOnFintype (EquivariantRing N) (Fin a)
    (fun _ ↦ EquivariantRing N)
  let eB := DirectSum.linearEquivFunOnFintype (EquivariantRing N) (Fin b)
    (fun _ ↦ EquivariantRing N)
  eB.toLinearMap.comp (f.hom.comp eA.symm.toLinearMap)

private theorem fromFreeHom_id {N a : ℕ} (s : Fin a → ℤ) :
    fromFreeHom (𝟙 (GradedModuleCat.free (EquivariantRing.grading N) s)) = LinearMap.id := by
  ext v j
  simp [fromFreeHom]

private theorem fromFreeHom_comp {N a b c : ℕ} {sa : Fin a → ℤ} {sb : Fin b → ℤ} {sc : Fin c → ℤ}
    (f : GradedModuleCat.free (EquivariantRing.grading N) sa ⟶
      GradedModuleCat.free (EquivariantRing.grading N) sb)
    (g : GradedModuleCat.free (EquivariantRing.grading N) sb ⟶
      GradedModuleCat.free (EquivariantRing.grading N) sc) :
    fromFreeHom (f ≫ g) = (fromFreeHom g).comp (fromFreeHom f) :=
  LinearMap.ext fun v ↦ by
    simp only [fromFreeHom, GradedModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

private theorem fromFreeHom_mem_grading {N a b : ℕ} {sa : Fin a → ℤ} {sb : Fin b → ℤ}
    (f : GradedModuleCat.free (EquivariantRing.grading N) sa ⟶
      GradedModuleCat.free (EquivariantRing.grading N) sb)
    (q : ℤ) (w : Fin a → EquivariantRing N)
    (hw : ∀ i, w i ∈ EquivariantRing.grading N (q - sa i)) (j : Fin b) :
    fromFreeHom f w j ∈ EquivariantRing.grading N (q - sb j) := by
  let eA := DirectSum.linearEquivFunOnFintype (EquivariantRing N) (Fin a)
    (fun _ ↦ EquivariantRing N)
  exact (GradedModuleCat.mem_free_piece_iff _ sb q (f.hom (eA.symm w))).mp
    (GradedModuleCat.map_mem f <|
      (GradedModuleCat.mem_free_piece_iff _ sa q (eA.symm w)).mpr fun i ↦ by
        simpa only [show (eA.symm w) i = w i from congrFun (eA.apply_symm_apply w) i] using hw i) j

/-- **Homogeneous retract splitting over `EquivariantRing N`.** Let `p` be a degree-zero idempotent
`EquivariantRing N`-linear endomorphism of the shifted free module `Fin m → EquivariantRing N`
with source shifts `s : Fin m → ℤ`. Then `p` factors through `Fin n → EquivariantRing N` for
target shifts `d : Fin n → ℤ` via degree-preserving maps `ι` and `π` satisfying `ι.comp π = p`
and `π.comp ι = LinearMap.id`, and the columns `ι (Pi.single i 1)` form a homogeneous
`EquivariantRing N`-basis of `LinearMap.range p`. -/
theorem exists_homogeneous_retract_of_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
      (π : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin n → EquivariantRing N))
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p)),
      ι.comp π = p ∧
        π.comp ι = LinearMap.id ∧
        (∀ (q : ℤ) (w : Fin n → EquivariantRing N),
          (∀ i, w i ∈ EquivariantRing.grading N (q - d i)) →
          ∀ j, ι w j ∈ EquivariantRing.grading N (q - s j)) ∧
        (∀ (q : ℤ) (v : Fin m → EquivariantRing N),
          (∀ j, v j ∈ EquivariantRing.grading N (q - s j)) →
          ∀ i, π v i ∈ EquivariantRing.grading N (q - d i)) ∧
        ∀ i, (b i).val = ι (Pi.single i 1) ∧
          ∀ j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  let eM := DirectSum.linearEquivFunOnFintype (EquivariantRing N) (Fin m)
    (fun _ ↦ EquivariantRing N)
  let pFree : GradedModuleCat.free (EquivariantRing.grading N) s →ₗ[EquivariantRing N]
      GradedModuleCat.free (EquivariantRing.grading N) s :=
    eM.symm.toLinearMap.comp (p.comp eM.toLinearMap)
  have hpFree : LinearMap.IsHomogeneous pFree
      (GradedModuleCat.free (EquivariantRing.grading N) s).grading.piece
      (GradedModuleCat.free (EquivariantRing.grading N) s).grading.piece 0 :=
    LinearMap.isHomogeneous_def.mpr fun q u hu ↦ by
      rw [add_zero]
      refine (GradedModuleCat.mem_free_piece_iff _ s q _).mpr fun j ↦ ?_
      simpa only [pFree, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        show (eM.symm (p (eM u))) j = p (eM u) j from congrFun (eM.apply_symm_apply _) j] using
        hhom q (eM u) ((GradedModuleCat.mem_free_piece_iff _ s q u).mp hu) j
  let eCat := GradedModuleCat.ofHom pFree hpFree
  have heCat : eCat ≫ eCat = eCat := GradedModuleCat.hom_ext <| LinearMap.ext fun u ↦ by
    have hpp : p (p (eM u)) = p (eM u) := LinearMap.congr_fun hp (eM u)
    change eM.symm (p (eM (eM.symm (p (eM u))))) = eM.symm (p (eM u))
    rw [eM.apply_symm_apply, hpp]
  obtain ⟨n, d, ιCat, πCat, -, hπιCat, hιπCat, -⟩ :=
    GradedModuleCat.exists_free_retract_of_idempotent
      (EquivariantRing.grading_eq_bot_of_lt_zero N) eCat heCat
  let ι := fromFreeHom ιCat
  let π := fromFreeHom πCat
  have hιπ : ι.comp π = p := by
    rw [← fromFreeHom_comp, hπιCat]
    exact LinearMap.ext fun v ↦ by simp [fromFreeHom, eCat, pFree, eM]
  have hπι : π.comp ι = LinearMap.id := by
    rw [← fromFreeHom_comp, hιπCat, fromFreeHom_id]
  let b := (Pi.basisFun (EquivariantRing N) (Fin n)).map (retractLinearEquivRange ι π hιπ hπι)
  refine ⟨n, d, ι, π, b, hιπ, hπι, fromFreeHom_mem_grading ιCat, fromFreeHom_mem_grading πCat,
    fun i ↦ ⟨by simp [b], ?_⟩⟩
  simp only [b, Module.Basis.map_apply, Pi.basisFun_apply, coe_retractLinearEquivRange_apply]
  refine fromFreeHom_mem_grading ιCat (d i) (Pi.single i 1) (fun k ↦ ?_)
  by_cases hik : k = i
  · subst hik; simpa only [Pi.single_eq_same, sub_self] using SetLike.one_mem_graded _
  · simp only [Pi.single_eq_of_ne hik, Submodule.zero_mem]

/-- The image of a degree-zero idempotent on a finite sum of shifted copies of `EquivariantRing N`
has a finite homogeneous basis, where the `j`-th source summand has shift `s j`. -/
theorem exists_homogeneous_basis_range_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
      (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  obtain ⟨n, d, _, _, b, _, _, _, _, hb⟩ :=
    exists_homogeneous_retract_of_idempotent N m s p hp hhom
  exact ⟨n, b, d, fun i j ↦ (hb i).2 j⟩

namespace EquivariantRing

private def basisFinOneOfSpanSingleton {N m : ℕ}
    {U : Submodule (EquivariantRing N) (Fin m → EquivariantRing N)}
    {v₀ : Fin m → EquivariantRing N} (hv₀_ne : v₀ ≠ 0)
    (hU : U = Submodule.span (EquivariantRing N) {v₀}) :
    Module.Basis (Fin 1) (EquivariantRing N) U := by
  have hv₀_mem : v₀ ∈ U := hU ▸ Submodule.mem_span_singleton_self v₀
  let f₁ : (Fin 1 →₀ EquivariantRing N) →ₗ[EquivariantRing N] U :=
    (Finsupp.lapply (R := EquivariantRing N) (M := EquivariantRing N) (0 : Fin 1)).smulRight
      ⟨v₀, hv₀_mem⟩
  refine Module.Basis.ofRepr (LinearEquiv.ofBijective f₁ ⟨fun f g hfg ↦ Finsupp.ext fun t ↦ ?_,
    fun ⟨y, hy⟩ ↦ ?_⟩).symm
  · obtain ⟨j₀, hj₀⟩ : ∃ j, v₀ j ≠ 0 := Function.ne_iff.mp hv₀_ne
    rw [Subsingleton.elim t 0]
    have h := congrFun (congrArg Subtype.val hfg) j₀
    exact mul_right_cancel₀ hj₀
      (by simpa only [f₁, LinearMap.smulRight_apply, Finsupp.lapply_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul] using h)
  · have hy' : y ∈ Submodule.span (EquivariantRing N) {v₀} := hU ▸ hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    exact ⟨Finsupp.single 0 c, Subtype.ext (by simp [f₁])⟩

/-- When a submodule `U` of `Fin m → EquivariantRing N` is spanned by a single non-zero homogeneous
vector `v₀` of shifted degree `d₀`, every finite homogeneous basis `(n, b, d)` of `U` has `n = 1`
and generator degree `d₀`. -/
theorem eq_one_and_deg_eq_of_span_singleton {N m : ℕ} {s : Fin m → ℤ}
    {U : Submodule (EquivariantRing N) (Fin m → EquivariantRing N)}
    {v₀ : Fin m → EquivariantRing N} {d₀ : ℤ}
    (hv₀_ne : v₀ ≠ 0) (hU : U = Submodule.span (EquivariantRing N) {v₀})
    (hv₀_hom : ∀ j, v₀ j ∈ grading N (d₀ - s j))
    {n : ℕ} (b : Module.Basis (Fin n) (EquivariantRing N) U)
    {d : Fin n → ℤ} (hb : ∀ i j, (b i).val j ∈ grading N (d i - s j)) :
    n = 1 ∧ ∀ i, d i = d₀ := by
  have hn : n = 1 :=
    Fin.equiv_iff_eq.mp ⟨b.indexEquiv (basisFinOneOfSpanSingleton hv₀_ne hU)⟩
  subst hn
  refine ⟨rfl, fun i ↦ ?_⟩
  rw [Subsingleton.elim i 0]
  obtain ⟨j₀, hj₀⟩ : ∃ j, v₀ j ≠ 0 := Function.ne_iff.mp hv₀_ne
  have hv₀_mem : v₀ ∈ U := hU ▸ Submodule.mem_span_singleton_self v₀
  have hb0_mem : (b 0).val ∈ Submodule.span (EquivariantRing N) {v₀} := hU ▸ (b 0).property
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hb0_mem
  have hv₀_repr : v₀ = b.repr ⟨v₀, hv₀_mem⟩ 0 • (b 0).val := by
    have h := congrArg Subtype.val (b.sum_repr ⟨v₀, hv₀_mem⟩).symm
    simpa [Fin.sum_univ_one] using h
  have hunit : b.repr ⟨v₀, hv₀_mem⟩ 0 * u = 1 := by
    apply mul_right_cancel₀ hj₀
    have h := congrFun hv₀_repr j₀
    rw [← hu] at h
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, one_mul] using h.symm
  have hconst : MvPolynomial.constantCoeff u ≠ 0 := fun hc ↦ by
    have := congrArg MvPolynomial.constantCoeff hunit
    simp [map_mul, hc] at this
  have hdec0 : (DirectSum.decompose (grading N) u 0 : EquivariantRing N) =
      MvPolynomial.C (MvPolynomial.constantCoeff u) := by
    change (MvPolynomial.weightedGradedAlgebra ℤ (weight N) |>.decompose' u 0 :
      EquivariantRing N) = _
    rw [MvPolynomial.weightedDecomposition.decompose'_apply,
      MvPolynomial.weightedHomogeneousComponent_zero_of_pos (weight_pos N) u,
      MvPolynomial.constantCoeff_eq]
  have hcomp_ne : (DirectSum.decompose (grading N) ((b 0).val j₀) (d₀ - s j₀) :
      EquivariantRing N) ≠ 0 := by
    have hbj : (b 0).val j₀ = u * v₀ j₀ := by rw [← hu, Pi.smul_apply, smul_eq_mul]
    have hmul := DirectSum.coe_decompose_mul_add_of_right_mem (grading N) (i := 0) (a := u)
      (hv₀_hom j₀)
    rw [zero_add, ← hbj, hdec0] at hmul
    rw [hmul]
    exact mul_ne_zero (by simpa using hconst) hj₀
  by_contra hne
  have hne' : d 0 - s j₀ ≠ d₀ - s j₀ := fun h ↦ hne (by omega)
  exact hcomp_ne (by rw [DirectSum.decompose_of_mem_ne (grading N) (hb 0 j₀) hne'])

section Checks

-- Roadmap Check 1a: for `p = 0`, any homogeneous basis of `LinearMap.range p` has rank `0`.
example (N m : ℕ) (s : Fin m → ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
          (Fin m → EquivariantRing N))))
      (d : Fin n → ℤ),
      n = 0 ∧ ∀ i j, (b i).val j ∈ grading N (d i - s j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N m s 0 (by ext; simp)
    (fun _ _ _ _ ↦ by simp)
  have hn : n = 0 := by
    by_contra! hpos
    have hsub : Subsingleton (LinearMap.range
        (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))) := by
      rw [LinearMap.range_zero]
      infer_instance
    exact b.ne_zero ⟨0, Nat.pos_of_ne_zero hpos⟩ (hsub.elim _ _)
  exact ⟨n, b, d, hn, hb⟩

-- Roadmap Check 1b: for `p = id` on a rank-one summand of shift `3`, the basis has rank `1` and
-- degree `3`.
example (N : ℕ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (LinearMap.id :
          (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 1 → EquivariantRing N))))
      (d : Fin n → ℤ),
      n = 1 ∧ (∀ i, d i = 3) ∧ ∀ i j, (b i).val j ∈ grading N (d i - (![3] : Fin 1 → ℤ) j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 1 ![3] LinearMap.id rfl
    (fun _ _ hv j ↦ hv j)
  have hU : LinearMap.range (LinearMap.id :
      (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 1 → EquivariantRing N)) =
      Submodule.span (EquivariantRing N) {![1]} :=
    le_antisymm
      (fun y _ ↦ Submodule.mem_span_singleton.mpr ⟨y 0, funext fun j ↦ by fin_cases j; simp⟩)
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨![1], rfl⟩))
  obtain ⟨hn, hd⟩ := eq_one_and_deg_eq_of_span_singleton (d₀ := 3)
    (fun h ↦ one_ne_zero (congrFun h 0)) hU
    (fun j ↦ by fin_cases j; simpa using SetLike.one_mem_graded (grading N)) b hb
  exact ⟨n, b, d, hn, hd, hb⟩

-- Roadmap Check 2: for `p = diag(1, 0)` on `Λ_N{a} ⊕ Λ_N{b}`, the image basis has rank `1` and
-- degree `a`, independently of `b`.
example (N : ℕ) (a bShift : ℤ) :
    let p : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 2 → EquivariantRing N) :=
      { toFun := fun v ↦ ![v 0, 0]
        map_add' := fun u v ↦ funext fun j ↦ by fin_cases j <;> simp
        map_smul' := fun r v ↦ funext fun j ↦ by fin_cases j <;> simp }
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      n = 1 ∧ (∀ i, d i = a) ∧
        ∀ i j, (b i).val j ∈ grading N (d i - (![a, bShift] : Fin 2 → ℤ) j) := by
  intro p
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 2 ![a, bShift] p
    (LinearMap.ext fun v ↦ funext fun j ↦ by fin_cases j <;> simp [p])
    (fun q v hv j ↦ by
      fin_cases j
      · exact hv 0
      · exact Submodule.zero_mem _)
  have hU : LinearMap.range p = Submodule.span (EquivariantRing N) {![1, 0]} :=
    le_antisymm
      (by rintro _ ⟨v, rfl⟩; exact Submodule.mem_span_singleton.mpr
            ⟨v 0, funext fun j ↦ by fin_cases j <;> simp [p]⟩)
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨![1, 0], rfl⟩))
  obtain ⟨hn, hd⟩ := eq_one_and_deg_eq_of_span_singleton (d₀ := a)
    (fun h ↦ one_ne_zero (congrFun h 0)) hU
    (fun j ↦ by
      fin_cases j
      · simpa using SetLike.one_mem_graded (grading N)
      · exact Submodule.zero_mem _) b hb
  exact ⟨n, b, d, hn, hd, hb⟩

-- Roadmap Check 3: on `EquivariantRing (N + 1)` with shifts `(2, 0)` and `p(x, y) = (x, e₁ x)`,
-- `p` is a degree-zero idempotent and every homogeneous basis of `LinearMap.range p` has rank `1`
-- and degree `2` (verifying `2 - 0 = 2 = deg e₁`, the shift sign).
example (N : ℕ) :
    let e₁ : EquivariantRing (N + 1) := MvPolynomial.X 0
    let p : (Fin 2 → EquivariantRing (N + 1)) →ₗ[EquivariantRing (N + 1)]
        (Fin 2 → EquivariantRing (N + 1)) :=
      { toFun := fun v ↦ ![v 0, e₁ * v 0]
        map_add' := fun u v ↦ funext fun j ↦ by fin_cases j <;> simp [mul_add]
        map_smul' := fun r v ↦ funext fun j ↦ by fin_cases j <;> simp [smul_eq_mul]; ring }
    p.comp p = p ∧
      ∃ (n : ℕ) (b : Module.Basis (Fin n) (EquivariantRing (N + 1)) (LinearMap.range p))
        (d : Fin n → ℤ),
        n = 1 ∧ (∀ i, d i = 2) ∧
          ∀ i j, (b i).val j ∈ grading (N + 1) (d i - (![2, 0] : Fin 2 → ℤ) j) := by
  intro e₁ p
  have hp : p.comp p = p := LinearMap.ext fun v ↦ funext fun j ↦ by fin_cases j <;> simp [p]
  have hhom : ∀ (q : ℤ) (v : Fin 2 → EquivariantRing (N + 1)),
      (∀ j, v j ∈ grading (N + 1) (q - (![2, 0] : Fin 2 → ℤ) j)) →
      ∀ j, p v j ∈ grading (N + 1) (q - (![2, 0] : Fin 2 → ℤ) j) := fun q v hv j ↦ by
    fin_cases j
    · exact hv 0
    · have he₁ : e₁ ∈ grading (N + 1) 2 := by simpa [e₁] using X_mem_grading (N + 1) 0
      have hv0 : v 0 ∈ grading (N + 1) (q - 2) := hv 0
      simpa [p, show 2 + (q - 2) = q by omega] using SetLike.mul_mem_graded he₁ hv0
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent (N + 1) 2 ![2, 0] p hp hhom
  have hU : LinearMap.range p = Submodule.span (EquivariantRing (N + 1)) {![1, e₁]} :=
    le_antisymm
      (by rintro _ ⟨v, rfl⟩; exact Submodule.mem_span_singleton.mpr ⟨v 0, funext fun j ↦ by
            fin_cases j
            · simp [p]
            · dsimp [p]; exact mul_comm _ _⟩)
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
        ⟨![1, 0], by ext j; fin_cases j <;> simp [p]⟩))
  obtain ⟨hn, hd⟩ := eq_one_and_deg_eq_of_span_singleton (d₀ := 2)
    (fun h ↦ one_ne_zero (congrFun h 0)) hU
    (fun j ↦ by
      fin_cases j
      · simpa using SetLike.one_mem_graded (grading (N + 1))
      · simpa [e₁] using X_mem_grading (N + 1) 0) b hb
  exact ⟨hp, n, b, d, hn, hd, hb⟩

end Checks

end EquivariantRing

end TauCeti
