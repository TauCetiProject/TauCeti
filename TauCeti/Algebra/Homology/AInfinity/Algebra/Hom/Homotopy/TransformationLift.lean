/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Transformation
public import TauCeti.Algebra.Homology.Contraction.Linear.HomotopyEquiv
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# Lifting reduced transformations along homotopy equivalences on linear parts

Let `f : A ⟶ B` be an `A∞` morphism over a commutative ring `R` whose linear part `f₁` extends to a
graded `TauCeti.LinearHomotopyEquiv` between the unary differentials of `A` and `B`.  For any two
`A∞` morphisms `v₁, v₂ : C ⟶ A`, postcomposition with `f` induces a cochain map
`reducedTransformationComplexCompRight v₁ v₂ f` from `reducedTransformationComplex v₁ v₂` to
`reducedTransformationComplex (f ∘ v₁) (f ∘ v₂)`.

By induction on the word-length filtration of `Tᶜ(sC)`—decomposing the bar differential into its
length-preserving unary part and filtration-decreasing higher part and solving coupled obstruction
equations on each word length via `LinearHomotopyEquiv.obstructionLift` and
`LinearHomotopyEquiv.obstructionHomotopy`—every coupled cocycle-coboundary problem along
postcomposition with `f` has a global solution
(`TauCeti.AInfinityHom.exists_reducedTransformationCochains_of_compRight`).

Two immediate consequences follow:

* `TauCeti.AInfinityHom.Homotopy.ofCompRightOfLinearHomotopyEquiv`: homotopies between `f ∘ v₁`
  and `f ∘ v₂` lift to homotopies between `v₁` and `v₂`.
* `TauCeti.AInfinityHom.quasiIso_reducedTransformationComplexCompRight_of_linearHomotopyEquiv`:
  `reducedTransformationComplexCompRight v₁ v₂ f` is a quasi-isomorphism of cochain complexes.

## Main definitions and results

* `TauCeti.AInfinityAlgebra.isHomogeneous_differential`: the unary differential has degree one.
* `TauCeti.AInfinityAlgebra.lengthProj_comp_unaryBarDifferential`: word-length projections commute
  with the unary bar differential.
* `TauCeti.AInfinityHom.exists_reducedTransformationCochains_of_compRight`: coupled lifting of
  reduced transformations along `f`.
* `TauCeti.AInfinityHom.Homotopy.ofCompRightOfLinearHomotopyEquiv`: left cancellation of `f` on
  `A∞` homotopies.
* `TauCeti.AInfinityHom.quasiIso_reducedTransformationComplexCompRight_of_linearHomotopyEquiv`:
  quasi-isomorphism of reduced transformation complexes under postcomposition with `f`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Section 1.3.3.
-/

public section

open scoped DirectSum
open CategoryTheory

namespace TauCeti

universe u uR uA uB uC

namespace ReducedTensorWords

section FiltrationAssembly

variable {R : Type uR} {C : Type uC} {M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [AddCommMonoid M] [Module R M]

/-- Assembles a sequence of linear maps `t n` on `ReducedTensorWords R C` by reading `t k` on words
of length `k`. -/
noncomputable def assembleFiltration
    (t : ℕ → ReducedTensorWords R C →ₗ[R] M) : ReducedTensorWords R C →ₗ[R] M :=
  DirectSum.toModule R {k : ℕ // 0 < k} M fun k ↦ t k.1 ∘ₗ ReducedTensorWords.of R C k

/-- On a word of length `k`, `assembleFiltration t` evaluates `t k.1`. -/
@[simp]
theorem assembleFiltration_of
    (t : ℕ → ReducedTensorWords R C →ₗ[R] M) (k : {k : ℕ // 0 < k}) (x : TensorPower R k.1 C) :
    assembleFiltration t (ReducedTensorWords.of R C k x) =
      t k.1 (ReducedTensorWords.of R C k x) := by
  rw [assembleFiltration, ReducedTensorWords.toModule_of, LinearMap.comp_apply]

private theorem filtration_apply_eq_of_le
    {t : ℕ → ReducedTensorWords R C →ₗ[R] M}
    (ht : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n, t (n + 1) z = t n z)
    {m n : ℕ} (hmn : m ≤ n) {z : ReducedTensorWords R C}
    (hz : z ∈ ReducedTensorWords.filtration R C m) : t n z = t m z := by
  induction hmn with
  | refl => rfl
  | @step k hmk ih =>
      exact (ht k z (ReducedTensorWords.filtration_monotone R C hmk hz)).trans ih

/-- On `filtration R C n`, `assembleFiltration t` agrees with `t n` whenever `t (k + 1)` agrees
with `t k` on `filtration R C k` for all `k`. -/
theorem assembleFiltration_apply_of_mem_filtration
    {t : ℕ → ReducedTensorWords R C →ₗ[R] M}
    (ht : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n, t (n + 1) z = t n z)
    {n : ℕ} {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    assembleFiltration t z = t n z := by
  have hle : ReducedTensorWords.filtration R C n ≤
      LinearMap.eqLocus (assembleFiltration t) (t n) := by
    rw [ReducedTensorWords.filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, assembleFiltration_of]
    exact (filtration_apply_eq_of_le ht hk
      (ReducedTensorWords.of_mem_filtration R C le_rfl x)).symm
  exact hle hz

/-- A map supported on words of length `n + 1` vanishes on `filtration R C n`. -/
theorem apply_eq_zero_of_comp_lengthProj_succ_eq
    {F : ReducedTensorWords R C →ₗ[R] M} {n : ℕ}
    (hF : F ∘ₗ ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩ = F)
    {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    F z = 0 := by
  rw [← hF, LinearMap.comp_apply,
    ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R C (Nat.lt_succ_self n) hz,
    map_zero]

end FiltrationAssembly

/-- If every `t n` is homogeneous of degree `p`, then so is `assembleFiltration t`. -/
theorem isHomogeneous_assembleFiltration {R : Type uR} {C : Type uC} {M σM : Type*}
    [CommRing R] [AddCommMonoid C] [Module R C] [AddCommMonoid M]
    [Module R M] [SetLike σM M] [AddMemClass σM M] [SMulMemClass σM R M]
    {G : InternalGrading R C ℤ} {ℳ : ℤ → σM} {p : ℤ} {t : ℕ → ReducedTensorWords R C →ₗ[R] M}
    (ht : ∀ n, LinearMap.IsHomogeneous (t n) (ReducedTensorWords.gradedPiece G) ℳ p) :
    LinearMap.IsHomogeneous (assembleFiltration t) (ReducedTensorWords.gradedPiece G) ℳ p := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine ReducedTensorWords.gradedPiece_induction
    (motive := fun w ↦ assembleFiltration t w ∈ ℳ (D + p)) hz
    (fun k hk 𝒟 x hx hD ↦ ?_)
    (fun u v _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun c u _ hu ↦ by rw [map_smul]; exact SMulMemClass.smul_mem c hu)
  rw [assembleFiltration_of]
  exact (ht k).map_mem (hD ▸ ReducedTensorWords.mem_gradedPiece_of_tprod G hk x 𝒟 hx)

end ReducedTensorWords

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityAlgebra

/-- The unary differential of an `A∞` algebra has degree one. -/
theorem isHomogeneous_differential (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.differential 𝒜.grading.piece 𝒜.grading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.differential_mem_piece hx

/-- Every word-length projection commutes with the unary bar differential. -/
theorem lengthProj_comp_unaryBarDifferential (𝒜 : AInfinityAlgebra R A)
    (m : {n : ℕ // 0 < n}) :
    ReducedTensorWords.lengthProj R A m ∘ₗ 𝒜.unaryBarDifferential =
      𝒜.unaryBarDifferential ∘ₗ ReducedTensorWords.lengthProj R A m := by
  rw [𝒜.unaryBarDifferential_eq_gradedCoderiv]
  refine ReducedTensorWords.lengthProj_comp_gradedCoderiv (𝒜.grading.shift 1) 1
    (a := (1 : {n : ℕ // 0 < n})) ?_ rfl
  refine ReducedTensorWords.linearMap_ext R A fun k x ↦ ?_
  by_cases hk : k = 1
  · subst hk
    rw [LinearMap.comp_apply, ReducedTensorWords.lengthProj_of_self]
  · rw [LinearMap.comp_apply, ReducedTensorWords.lengthProj_of_of_ne R A hk, map_zero,
      LinearMap.comp_apply, ReducedTensorWords.letter_of_of_ne_one R A hk, map_zero]

end AInfinityAlgebra

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- Shifts `LinearHomotopyEquiv.IsGraded` from the internal gradings to the suspended gradings. -/
theorem isGraded_shift_one {e : LinearHomotopyEquiv AA.differential BB.differential}
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1) :
    e.IsGraded (AA.grading.shift 1).piece (BB.grading.shift 1).piece 1 :=
  ⟨LinearMap.isHomogeneous_shift_piece_iff.2 he.hom,
    LinearMap.isHomogeneous_shift_piece_iff.2 he.inv,
    LinearMap.isHomogeneous_shift_piece_iff.2 he.homotopyHomInv,
    LinearMap.isHomogeneous_shift_piece_iff.2 he.homotopyInvHom⟩

/-- Evaluating `t (b_unary (π z))` agrees with `(t ∘ₗ π) (b_unary z)` because `π` commutes with
`b_unary`. -/
theorem taylor_lengthProj_unaryBarDifferential {M : Type*} [AddCommMonoid M] [Module R M]
    (CC : AInfinityAlgebra R C) (t : ReducedTensorWords R C →ₗ[R] M) (n : {n : ℕ // 0 < n})
    (z : ReducedTensorWords R C) :
    t (CC.unaryBarDifferential (ReducedTensorWords.lengthProj R C n z)) =
      (t ∘ₗ ReducedTensorWords.lengthProj R C n) (CC.unaryBarDifferential z) := by
  have hcomm := LinearMap.congr_fun (CC.lengthProj_comp_unaryBarDifferential n) z
  simp only [LinearMap.comp_apply] at hcomm ⊢
  rw [← hcomm]

/-- On words of length at most `n + 1`, the differential of a transformation vanishing up to length
`n` has Taylor map `d_A ∘ taylor X - (-1)^p taylor X ∘ b_unary`. -/
private theorem taylor_reducedTransformationDifferential_of_mem_filtration_succ
    {v₁ v₂ : AInfinityHom CC AA} {p : ℤ} {n : ℕ} {X : reducedTransformationCochains v₁ v₂ p}
    (hl : ∀ u ∈ ReducedTensorWords.filtration R C n, reducedTransformationCochains.taylor X u = 0)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    reducedTransformationCochains.taylor (reducedTransformationDifferential v₁ v₂ p X) w =
      AA.differential (reducedTransformationCochains.taylor X w) -
        ((p.negOnePow : ℤ) : R) •
          reducedTransformationCochains.taylor X (CC.unaryBarDifferential w) := by
  have hX₀ : ∀ u ∈ ReducedTensorWords.filtration R C n,
      (X : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) u = 0 :=
    fun _ hu ↦ reducedTransformationCochains.apply_eq_zero_of_mem_filtration hl hu
  have hXw := reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ hX₀ hw
  have hhigh : reducedTransformationCochains.taylor X (CC.higherBarDifferential w) = 0 :=
    hl _ (CC.higherBarDifferential_filtration n ⟨w, hw, rfl⟩)
  rw [reducedTransformationCochains.taylor_reducedTransformationDifferential, LinearMap.sub_apply,
    LinearMap.comp_apply, hXw, AA.taylor_ofLetter, ← AA.differential_apply,
    CC.barDifferential_eq_unary_add_higher, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.add_apply, map_add, hhigh, add_zero, Units.smul_def, ← Int.cast_smul_eq_zsmul R]

/-- On words of length at most `n + 1`, postcomposing a transformation vanishing up to length `n`
applies the linear part of `f` to its Taylor map. -/
private theorem taylor_compRight_of_mem_filtration_succ {v₁ v₂ : AInfinityHom CC AA}
    (f : AInfinityHom AA BB) {p : ℤ} {n : ℕ} {X : reducedTransformationCochains v₁ v₂ p}
    (hl : ∀ u ∈ ReducedTensorWords.filtration R C n, reducedTransformationCochains.taylor X u = 0)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    reducedTransformationCochains.taylor (reducedTransformationCochains.compRight f p X) w =
      f.linearPart (reducedTransformationCochains.taylor X w) := by
  have hX₀ : ∀ u ∈ ReducedTensorWords.filtration R C n,
      (X : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) u = 0 :=
    fun _ hu ↦ reducedTransformationCochains.apply_eq_zero_of_mem_filtration hl hu
  rw [reducedTransformationCochains.taylor_compRight, LinearMap.comp_apply,
    reducedTransformationCochains.apply_eq_ofLetter_of_mem_filtration_succ hX₀ hw,
    linearPart_apply]

/-- Partial solution up to word length `n` for coupled transformation lifting. -/
private structure TransformationLiftStep {v₁ v₂ : AInfinityHom CC AA} (f : AInfinityHom AA BB)
    {r : ℤ} (D : reducedTransformationCochains v₁ v₂ (r + 1 + 1))
    (K : reducedTransformationCochains (f.comp v₁) (f.comp v₂) (r + 1)) (n : ℕ) where
  L : reducedTransformationCochains v₁ v₂ (r + 1)
  M : reducedTransformationCochains (f.comp v₁) (f.comp v₂) r
  hL : ∀ z ∈ ReducedTensorWords.filtration R C n,
    reducedTransformationCochains.taylor (reducedTransformationDifferential v₁ v₂ (r + 1) L - D) z =
      0
  hM : ∀ z ∈ ReducedTensorWords.filtration R C n,
    reducedTransformationCochains.taylor
      (reducedTransformationCochains.compRight f (r + 1) L +
        reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r M - K) z = 0

/-- Coupled obstruction equations and homogeneity for the length-`n + 1` defects of a
`TransformationLiftStep`. -/
private theorem transformationLiftStep_obstruction
    {f : AInfinityHom AA BB} {v₁ v₂ : AInfinityHom CC AA} {r : ℤ}
    {D : reducedTransformationCochains v₁ v₂ (r + 1 + 1)}
    (hD : reducedTransformationDifferential v₁ v₂ (r + 1 + 1) D = 0)
    {K : reducedTransformationCochains (f.comp v₁) (f.comp v₂) (r + 1)}
    (hK : reducedTransformationDifferential (f.comp v₁) (f.comp v₂) (r + 1) K =
      reducedTransformationCochains.compRight f (r + 1 + 1) D)
    {n : ℕ} (s : TransformationLiftStep f D K n) :
    let E₁ := reducedTransformationDifferential v₁ v₂ (r + 1) s.L - D
    let E₂ := reducedTransformationCochains.compRight f (r + 1) s.L +
      reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r s.M - K
    let π := ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩
    let Φ := reducedTransformationCochains.taylor E₁ ∘ₗ π
    let Ψ := reducedTransformationCochains.taylor E₂ ∘ₗ π
    let ε : R := (((r + 1).negOnePow : ℤ) : R)
    (AA.differential ∘ₗ Φ + ε • (Φ ∘ₗ CC.unaryBarDifferential) = 0) ∧
      (BB.differential ∘ₗ Ψ - ε • (Ψ ∘ₗ CC.unaryBarDifferential) = f.linearPart ∘ₗ Φ) ∧
      LinearMap.IsHomogeneous Φ (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
        (AA.grading.shift 1).piece ((r + 1) + 1) ∧
      LinearMap.IsHomogeneous Ψ (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
        (BB.grading.shift 1).piece (r + 1) := by
  intro E₁ E₂ π Φ Ψ ε
  have hε₁ : (((r + 1 + 1).negOnePow : ℤ) : R) = -ε := by
    rw [Int.negOnePow_succ, Units.val_neg, Int.cast_neg]
  have hdE₁ : reducedTransformationDifferential v₁ v₂ (r + 1 + 1) E₁ = 0 := by
    simp only [E₁, map_sub, reducedTransformationDifferential_reducedTransformationDifferential, hD,
      sub_self]
  have hdE₂ : reducedTransformationDifferential (f.comp v₁) (f.comp v₂) (r + 1) E₂ =
      reducedTransformationCochains.compRight f (r + 1 + 1) E₁ := by
    simp only [E₂, E₁, map_sub, map_add, reducedTransformationDifferential_compRight,
      reducedTransformationDifferential_reducedTransformationDifferential, add_zero, hK]
  refine ⟨LinearMap.ext fun z ↦ ?_, LinearMap.ext fun z ↦ ?_, ?_, ?_⟩
  · have key := congrArg (fun X ↦ reducedTransformationCochains.taylor X (π z)) hdE₁
    rw [reducedTransformationCochains.taylor_zero, LinearMap.zero_apply,
      taylor_reducedTransformationDifferential_of_mem_filtration_succ s.hL
        (ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z),
      hε₁, neg_smul, sub_neg_eq_add,
      taylor_lengthProj_unaryBarDifferential CC (reducedTransformationCochains.taylor E₁)] at key
    simpa only [Φ, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] using key
  · have key := congrArg (fun X ↦ reducedTransformationCochains.taylor X (π z)) hdE₂
    rw [taylor_reducedTransformationDifferential_of_mem_filtration_succ s.hM
        (ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z),
      taylor_compRight_of_mem_filtration_succ f s.hL
        (ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z),
      taylor_lengthProj_unaryBarDifferential CC (reducedTransformationCochains.taylor E₂)] at key
    simpa only [Φ, Ψ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] using key
  · simpa only [Φ, π, zero_add] using (reducedTransformationCochains.isHomogeneous_taylor E₁).comp
      (ReducedTensorWords.isHomogeneous_lengthProj (CC.grading.shift 1) ⟨n + 1, n.succ_pos⟩)
  · simpa only [Ψ, π, zero_add] using (reducedTransformationCochains.isHomogeneous_taylor E₂).comp
      (ReducedTensorWords.isHomogeneous_lengthProj (CC.grading.shift 1) ⟨n + 1, n.succ_pos⟩)

/-- Verification of `hM` on `filtration R C (n + 1)` after subtracting `(Lγ, Mη)`. -/
private theorem transformationLiftStep_hM_succ
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    {v₁ v₂ : AInfinityHom CC AA} {r : ℤ}
    {D : reducedTransformationCochains v₁ v₂ (r + 1 + 1)}
    {K : reducedTransformationCochains (f.comp v₁) (f.comp v₂) (r + 1)}
    {n : ℕ} (s : TransformationLiftStep f D K n)
    {Lγ : reducedTransformationCochains v₁ v₂ (r + 1)}
    {Mη : reducedTransformationCochains (f.comp v₁) (f.comp v₂) r}
    (hγ₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, reducedTransformationCochains.taylor Lγ z = 0)
    (hη₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, reducedTransformationCochains.taylor Mη z = 0)
    (hsum : e.hom ∘ₗ reducedTransformationCochains.taylor Lγ +
        (BB.differential ∘ₗ reducedTransformationCochains.taylor Mη +
          (((r + 1).negOnePow : ℤ) : R) •
            (reducedTransformationCochains.taylor Mη ∘ₗ CC.unaryBarDifferential)) =
      reducedTransformationCochains.taylor
        (reducedTransformationCochains.compRight f (r + 1) s.L +
          reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r s.M - K) ∘ₗ
        ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    reducedTransformationCochains.taylor
      (reducedTransformationCochains.compRight f (r + 1) (s.L - Lγ) +
        reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r (s.M - Mη) - K) w = 0 := by
  set E₂ := reducedTransformationCochains.compRight f (r + 1) s.L +
    reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r s.M - K
  have hε₀ : ((r.negOnePow : ℤ) : R) = -(((r + 1).negOnePow : ℤ) : R) := by
    have hr : r.negOnePow = -(r + 1).negOnePow := by rw [Int.negOnePow_succ, neg_neg]
    rw [hr, Units.val_neg, Int.cast_neg]
  have hEq : reducedTransformationCochains.compRight f (r + 1) (s.L - Lγ) +
      reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r (s.M - Mη) - K =
      E₂ - (reducedTransformationCochains.compRight f (r + 1) Lγ +
        reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r Mη) := by
    simp only [E₂, map_sub]; abel
  rw [hEq, reducedTransformationCochains.taylor_sub, reducedTransformationCochains.taylor_add,
    LinearMap.sub_apply, LinearMap.add_apply, taylor_compRight_of_mem_filtration_succ f hγ₀ hw,
    taylor_reducedTransformationDifferential_of_mem_filtration_succ hη₀ hw,
    hε₀, neg_smul, sub_neg_eq_add, ← hf, ← LinearMap.comp_apply e.hom,
    ← LinearMap.comp_apply BB.differential,
    ← LinearMap.comp_apply (reducedTransformationCochains.taylor Mη),
    ← LinearMap.smul_apply, ← LinearMap.add_apply, ← LinearMap.add_apply,
    hsum, LinearMap.comp_apply, ReducedTensorWords.apply_lengthProj_of_mem_filtration R C s.hM hw,
    sub_self]

/-- Inductive step `n ↦ n + 1` for `TransformationLiftStep`, with stabilization on
`filtration R C n`. -/
private noncomputable def transformationLiftStepSucc
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    {v₁ v₂ : AInfinityHom CC AA} {r : ℤ}
    {D : reducedTransformationCochains v₁ v₂ (r + 1 + 1)}
    (hD : reducedTransformationDifferential v₁ v₂ (r + 1 + 1) D = 0)
    {K : reducedTransformationCochains (f.comp v₁) (f.comp v₂) (r + 1)}
    (hK : reducedTransformationDifferential (f.comp v₁) (f.comp v₂) (r + 1) K =
      reducedTransformationCochains.compRight f (r + 1 + 1) D)
    {n : ℕ} (s : TransformationLiftStep f D K n) :
    {s' : TransformationLiftStep f D K (n + 1) //
      (∀ z ∈ ReducedTensorWords.filtration R C n,
        reducedTransformationCochains.taylor s'.L z =
          reducedTransformationCochains.taylor s.L z) ∧
      (∀ z ∈ ReducedTensorWords.filtration R C n,
        reducedTransformationCochains.taylor s'.M z =
          reducedTransformationCochains.taylor s.M z)} := by
  set E₁ := reducedTransformationDifferential v₁ v₂ (r + 1) s.L - D
  set E₂ := reducedTransformationCochains.compRight f (r + 1) s.L +
    reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r s.M - K
  set π := ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩
  set Φ := reducedTransformationCochains.taylor E₁ ∘ₗ π
  set Ψ := reducedTransformationCochains.taylor E₂ ∘ₗ π
  obtain ⟨hΦ_eq, hΨ_eq, hΦ_hom, hΨ_hom⟩ := transformationLiftStep_obstruction hD hK s
  rw [← hf] at hΨ_eq
  have he' := isGraded_shift_one he
  set Lγ := reducedTransformationCochains.ofTaylor (f := v₁) (g := v₂) (p := r + 1)
    (e.obstructionLift Φ Ψ) (e.isHomogeneous_obstructionLift he' hΦ_hom hΨ_hom)
  set Mη := reducedTransformationCochains.ofTaylor (f := f.comp v₁) (g := f.comp v₂) (p := r)
    (e.obstructionHomotopy Φ Ψ)
    (by simpa only [add_sub_cancel_right] using
      e.isHomogeneous_obstructionHomotopy he' hΦ_hom hΨ_hom)
  have hγ₀ : ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor Lγ z = 0 := fun _ hz ↦ by
    rw [reducedTransformationCochains.taylor_ofTaylor]
    exact ReducedTensorWords.apply_eq_zero_of_comp_lengthProj_succ_eq
      (by rw [e.obstructionLift_comp, ReducedTensorWords.comp_lengthProj_comp_lengthProj,
        ReducedTensorWords.comp_lengthProj_comp_lengthProj]) hz
  have hη₀ : ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor Mη z = 0 := fun _ hz ↦ by
    rw [reducedTransformationCochains.taylor_ofTaylor]
    exact ReducedTensorWords.apply_eq_zero_of_comp_lengthProj_succ_eq
      (by rw [e.obstructionHomotopy_comp, ReducedTensorWords.comp_lengthProj_comp_lengthProj,
        ReducedTensorWords.comp_lengthProj_comp_lengthProj]) hz
  refine ⟨⟨s.L - Lγ, s.M - Mη, fun w hw ↦ ?_,
      fun w hw ↦ transformationLiftStep_hM_succ e hf s hγ₀ hη₀
        (by simpa only [Lγ, Mη, reducedTransformationCochains.taylor_ofTaylor] using
          e.hom_comp_obstructionLift_add hΦ_eq hΨ_eq) hw⟩,
    fun z hz ↦ by
      rw [reducedTransformationCochains.taylor_sub, LinearMap.sub_apply, hγ₀ z hz, sub_zero],
    fun z hz ↦ by
      rw [reducedTransformationCochains.taylor_sub, LinearMap.sub_apply, hη₀ z hz, sub_zero]⟩
  have hEq : reducedTransformationDifferential v₁ v₂ (r + 1) (s.L - Lγ) - D =
      E₁ - reducedTransformationDifferential v₁ v₂ (r + 1) Lγ := by
    simp only [E₁, map_sub]; abel
  rw [hEq, reducedTransformationCochains.taylor_sub, LinearMap.sub_apply,
    taylor_reducedTransformationDifferential_of_mem_filtration_succ hγ₀ hw,
    reducedTransformationCochains.taylor_ofTaylor, ← LinearMap.comp_apply AA.differential,
    ← LinearMap.comp_apply (e.obstructionLift Φ Ψ), ← LinearMap.smul_apply,
    ← LinearMap.sub_apply, e.dM_comp_obstructionLift_sub hΦ_eq hΨ_eq,
    LinearMap.comp_apply, ReducedTensorWords.apply_lengthProj_of_mem_filtration R C s.hL hw,
    sub_self]

/-- Assembles a filtration-stabilizing sequence in `reducedTransformationCochains` via its Taylor
maps. -/
private noncomputable def assembleTransformationCochains {v₁ v₂ : AInfinityHom CC AA} {p : ℤ}
    (X : ℕ → reducedTransformationCochains v₁ v₂ p) :
    reducedTransformationCochains v₁ v₂ p :=
  reducedTransformationCochains.ofTaylor
    (ReducedTensorWords.assembleFiltration fun n ↦ reducedTransformationCochains.taylor (X n))
    (ReducedTensorWords.isHomogeneous_assembleFiltration fun n ↦
      reducedTransformationCochains.isHomogeneous_taylor (X n))

private theorem taylor_assembleTransformationCochains_of_mem_filtration
    {v₁ v₂ : AInfinityHom CC AA} {p : ℤ} (X : ℕ → reducedTransformationCochains v₁ v₂ p)
    (hX : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (X (n + 1)) z =
        reducedTransformationCochains.taylor (X n) z)
    {n : ℕ} {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    reducedTransformationCochains.taylor (assembleTransformationCochains X) z =
      reducedTransformationCochains.taylor (X n) z := by
  rw [assembleTransformationCochains, reducedTransformationCochains.taylor_ofTaylor,
    ReducedTensorWords.assembleFiltration_apply_of_mem_filtration hX hz]

private theorem coe_assembleTransformationCochains_of_mem_filtration
    {v₁ v₂ : AInfinityHom CC AA} {p : ℤ} (X : ℕ → reducedTransformationCochains v₁ v₂ p)
    (hX : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (X (n + 1)) z =
        reducedTransformationCochains.taylor (X n) z)
    {n : ℕ} {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    (assembleTransformationCochains X :
        ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z =
      (X n : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) z :=
  reducedTransformationCochains.apply_eq_of_mem_filtration
    (fun _ hw ↦ taylor_assembleTransformationCochains_of_mem_filtration X hX hw) hz

private theorem taylor_differential_assembleTransformationCochains_of_mem_filtration
    {v₁ v₂ : AInfinityHom CC AA} {p : ℤ} (X : ℕ → reducedTransformationCochains v₁ v₂ p)
    (hX : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (X (n + 1)) z =
        reducedTransformationCochains.taylor (X n) z)
    {n : ℕ} {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    reducedTransformationCochains.taylor
        (reducedTransformationDifferential v₁ v₂ p (assembleTransformationCochains X)) z =
      reducedTransformationCochains.taylor
        (reducedTransformationDifferential v₁ v₂ p (X n)) z := by
  simp only [reducedTransformationCochains.taylor_reducedTransformationDifferential,
    LinearMap.sub_apply, LinearMap.comp_apply, Units.smul_def, LinearMap.smul_apply,
    coe_assembleTransformationCochains_of_mem_filtration X hX hz,
    taylor_assembleTransformationCochains_of_mem_filtration X hX
      (CC.barDifferential_mem_filtration hz)]

/-- **Coupled lifting of reduced transformations** along an `A∞` morphism `f : A ⟶ B` whose linear
part extends to a graded `LinearHomotopyEquiv`: given a closed transformation `D` of degree `q`
from `v₁` to `v₂` and a transformation `K` of degree `p` (`p + 1 = q`) bounding `f ∘ D`, there
exist transformations `L` of degree `p` and `M` of degree `r` (`r + 1 = p`) with `δ L = D` and
`f ∘ L + δ M = K`. -/
theorem exists_reducedTransformationCochains_of_compRight
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    (v₁ v₂ : AInfinityHom CC AA) {r p q : ℤ}
    (D : reducedTransformationCochains v₁ v₂ q)
    (hD : reducedTransformationDifferential v₁ v₂ q D = 0)
    (K : reducedTransformationCochains (f.comp v₁) (f.comp v₂) p)
    (hK : (reducedTransformationDifferential (f.comp v₁) (f.comp v₂) p K :
        ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
      reducedTransformationCochains.compRight f q D)
    (hrp : r + 1 = p) (hpq : p + 1 = q) :
    ∃ (L : reducedTransformationCochains v₁ v₂ p)
      (M : reducedTransformationCochains (f.comp v₁) (f.comp v₂) r),
      (reducedTransformationDifferential v₁ v₂ p L :
          ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) = D ∧
        (reducedTransformationCochains.compRight f p L :
            ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) +
          reducedTransformationDifferential (f.comp v₁) (f.comp v₂) r M = K := by
  subst hrp
  subst hpq
  have hK' : reducedTransformationDifferential (f.comp v₁) (f.comp v₂) (r + 1) K =
      reducedTransformationCochains.compRight f (r + 1 + 1) D := Subtype.ext hK
  let base : TransformationLiftStep f D K 0 :=
    { L := 0
      M := 0
      hL := ReducedTensorWords.apply_eq_zero_of_mem_filtration_zero R C _
      hM := ReducedTensorWords.apply_eq_zero_of_mem_filtration_zero R C _ }
  let seq : ∀ n, TransformationLiftStep f D K n :=
    Nat.rec base fun _ s ↦ (transformationLiftStepSucc e he hf hD hK' s).1
  have hstabL : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (seq (n + 1)).L z =
        reducedTransformationCochains.taylor (seq n).L z :=
    fun n ↦ (transformationLiftStepSucc e he hf hD hK' (seq n)).2.1
  have hstabM : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (seq (n + 1)).M z =
        reducedTransformationCochains.taylor (seq n).M z :=
    fun n ↦ (transformationLiftStepSucc e he hf hD hK' (seq n)).2.2
  let L := assembleTransformationCochains fun n ↦ (seq n).L
  let M := assembleTransformationCochains fun n ↦ (seq n).M
  refine ⟨L, M, ?_, ?_⟩
  · refine congrArg Subtype.val (reducedTransformationCochains.ext <| LinearMap.ext fun z ↦ ?_)
    obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R C z
    have hsub := (seq n).hL z hn
    rw [reducedTransformationCochains.taylor_sub, LinearMap.sub_apply,
      ← taylor_differential_assembleTransformationCochains_of_mem_filtration
        (fun k ↦ (seq k).L) hstabL hn] at hsub
    exact sub_eq_zero.1 hsub
  · rw [← Submodule.coe_add]
    refine congrArg Subtype.val (reducedTransformationCochains.ext <| LinearMap.ext fun z ↦ ?_)
    obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R C z
    have hcomp : reducedTransformationCochains.taylor
        (reducedTransformationCochains.compRight f (r + 1) L) z =
        reducedTransformationCochains.taylor
          (reducedTransformationCochains.compRight f (r + 1) (seq n).L) z := by
      simp only [L, reducedTransformationCochains.taylor_compRight, LinearMap.comp_apply,
        coe_assembleTransformationCochains_of_mem_filtration (fun k ↦ (seq k).L) hstabL hn]
    have hsub := (seq n).hM z hn
    rw [reducedTransformationCochains.taylor_sub, reducedTransformationCochains.taylor_add,
      LinearMap.sub_apply, LinearMap.add_apply, ← hcomp,
      ← taylor_differential_assembleTransformationCochains_of_mem_filtration
        (fun k ↦ (seq k).M) hstabM hn] at hsub
    rw [reducedTransformationCochains.taylor_add, LinearMap.add_apply]
    exact sub_eq_zero.1 hsub

/-- **Homotopies cancel on the left along a graded `LinearHomotopyEquiv`**: if `f ∘ v₁` and
`f ∘ v₂` are homotopic and `f₁` extends to a graded `LinearHomotopyEquiv`, then `v₁` and `v₂` are
homotopic. -/
noncomputable def Homotopy.ofCompRightOfLinearHomotopyEquiv
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    {v₁ v₂ : AInfinityHom CC AA} (h : Homotopy (f.comp v₁) (f.comp v₂)) :
    Homotopy v₁ v₂ :=
  let D : reducedTransformationCochains v₁ v₂ 0 :=
    ⟨v₁.barMap - v₂.barMap, barMap_sub_barMap_mem_reducedTransformationCochains v₁ v₂⟩
  have hK : (reducedTransformationDifferential (f.comp v₁) (f.comp v₂) (-1)
        (Homotopy.equivCochains h).1 :
        ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
      reducedTransformationCochains.compRight f 0 D := by
    rw [(Homotopy.equivCochains h).2, reducedTransformationCochains.coe_compRight,
      barMap_comp, barMap_comp, LinearMap.comp_sub]
  have hex := exists_reducedTransformationCochains_of_compRight e he hf v₁ v₂ D
    (reducedTransformationDifferential_barMap_sub_barMap v₁ v₂)
    (Homotopy.equivCochains h).1 hK (r := -2) (by decide) (by decide)
  Homotopy.equivCochains.symm ⟨hex.choose, hex.choose_spec.choose_spec.1⟩

section ComplexQuasiIso

variable {A' B' C' : Type u}
  [AddCommGroup A'] [Module R A']
  [AddCommGroup B'] [Module R B']
  [AddCommGroup C'] [Module R C']
  {AA' : AInfinityAlgebra R A'} {BB' : AInfinityAlgebra R B'} {CC' : AInfinityAlgebra R C'}

private theorem injective_homologyMap_reducedTransformationComplexCompRight
    (e : LinearHomotopyEquiv AA'.differential BB'.differential)
    (he : e.IsGraded AA'.grading.piece BB'.grading.piece 1)
    {f : AInfinityHom AA' BB'} (hf : e.hom = f.linearPart)
    (v₁ v₂ : AInfinityHom CC' AA') (p : ℤ) :
    Function.Injective
      (HomologicalComplex.homologyMap (reducedTransformationComplexCompRight v₁ v₂ f) (p + 1)) := by
  set K := reducedTransformationComplex v₁ v₂
  set L := reducedTransformationComplex (f.comp v₁) (f.comp v₂)
  set φ := reducedTransformationComplexCompRight v₁ v₂ f
  have hn : (ComplexShape.up ℤ).next (p + 1) = p + 1 + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev (p + 1) = p := (ComplexShape.up ℤ).prev_eq' rfl
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨⟨z, hz⟩, rfl⟩ := K.moduleCatKerHomologyClass_surjective hn c
  rw [HomologicalComplex.homologyMap_moduleCatKerHomologyClass hn φ ⟨z, hz⟩] at hc
  obtain ⟨⟨_, K₀, hK₀⟩, hinc⟩ :=
    ((L.exact_inclusion_moduleCatKerHomologyClass hn hp) _).1 hc
  have hK₀_eq : (L.d p (p + 1)).hom K₀ = (φ.f (p + 1)).hom z :=
    hK₀.trans (congrArg Subtype.val hinc)
  have hz' : reducedTransformationDifferential v₁ v₂ (p + 1) z = 0 :=
    (mem_ker_reducedTransformationComplex_d_iff z).1 hz
  have hK₀' : (reducedTransformationDifferential (f.comp v₁) (f.comp v₂) p K₀ :
      ReducedTensorWords R C' →ₗ[R] ReducedTensorWords R B') =
      reducedTransformationCochains.compRight f (p + 1) z :=
    ((reducedTransformationComplex_d_hom_eq_iff K₀ ((φ.f (p + 1)).hom z)).1 hK₀_eq).trans
      (coe_reducedTransformationComplexCompRight_f_hom_apply v₁ v₂ f (p + 1) z)
  obtain ⟨L₀, _, hL₀, _⟩ := exists_reducedTransformationCochains_of_compRight e he hf v₁ v₂
    z hz' K₀ hK₀' (sub_add_cancel p 1) rfl
  have hL₀' : (K.d p (p + 1)).hom L₀ = z :=
    (reducedTransformationComplex_d_hom_eq_iff L₀ z).2 hL₀
  exact ((K.exact_inclusion_moduleCatKerHomologyClass hn hp) ⟨z, hz⟩).2
    ⟨⟨z, L₀, hL₀'⟩, Subtype.ext rfl⟩

private theorem surjective_homologyMap_reducedTransformationComplexCompRight
    (e : LinearHomotopyEquiv AA'.differential BB'.differential)
    (he : e.IsGraded AA'.grading.piece BB'.grading.piece 1)
    {f : AInfinityHom AA' BB'} (hf : e.hom = f.linearPart)
    (v₁ v₂ : AInfinityHom CC' AA') (p : ℤ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (reducedTransformationComplexCompRight v₁ v₂ f) (p + 1)) := by
  set K := reducedTransformationComplex v₁ v₂
  set L := reducedTransformationComplex (f.comp v₁) (f.comp v₂)
  set φ := reducedTransformationComplexCompRight v₁ v₂ f
  have hn : (ComplexShape.up ℤ).next (p + 1) = p + 1 + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hp : (ComplexShape.up ℤ).prev (p + 1) = p := (ComplexShape.up ℤ).prev_eq' rfl
  intro d
  obtain ⟨⟨w, hw₀⟩, rfl⟩ := L.moduleCatKerHomologyClass_surjective hn d
  have hw : (reducedTransformationDifferential (f.comp v₁) (f.comp v₂) (p + 1) w :
      ReducedTensorWords R C' →ₗ[R] ReducedTensorWords R B') =
      reducedTransformationCochains.compRight f (p + 1 + 1)
        (0 : reducedTransformationCochains v₁ v₂ (p + 1 + 1)) := by
    rw [(mem_ker_reducedTransformationComplex_d_iff w).1 hw₀, map_zero, Submodule.coe_zero]
  obtain ⟨L₀, M₀, hL₀, hM₀⟩ := exists_reducedTransformationCochains_of_compRight e he hf v₁ v₂
    0 (map_zero _) w hw rfl rfl
  have hz₀ : L₀ ∈ LinearMap.ker (K.d (p + 1) (p + 1 + 1)).hom :=
    (mem_ker_reducedTransformationComplex_d_iff L₀).2 (Subtype.ext hL₀)
  refine ⟨K.moduleCatKerHomologyClass hn ⟨L₀, hz₀⟩, ?_⟩
  rw [HomologicalComplex.homologyMap_moduleCatKerHomologyClass hn φ ⟨L₀, hz₀⟩, eq_comm,
    ← sub_eq_zero, ← map_sub]
  have hM₀' : (L.d p (p + 1)).hom M₀ = w - (φ.f (p + 1)).hom L₀ :=
    (reducedTransformationComplex_d_hom_eq_iff M₀ (w - (φ.f (p + 1)).hom L₀)).2 <|
      ((eq_sub_of_add_eq' hM₀).trans
        (congrArg (w.1 - ·)
          (coe_reducedTransformationComplexCompRight_f_hom_apply v₁ v₂ f (p + 1) L₀).symm)).trans
        (coe_reducedTransformationComplex_X_sub w ((φ.f (p + 1)).hom L₀)).symm
  exact ((L.exact_inclusion_moduleCatKerHomologyClass hn hp) _).2
    ⟨⟨_, M₀, hM₀'⟩, Subtype.ext rfl⟩

/-- Postcomposing reduced transformations with an `A∞` morphism `f` whose linear part extends to a
graded `LinearHomotopyEquiv` is a quasi-isomorphism of cochain complexes. -/
theorem quasiIso_reducedTransformationComplexCompRight_of_linearHomotopyEquiv
    (e : LinearHomotopyEquiv AA'.differential BB'.differential)
    (he : e.IsGraded AA'.grading.piece BB'.grading.piece 1)
    {f : AInfinityHom AA' BB'} (hf : e.hom = f.linearPart)
    (v₁ v₂ : AInfinityHom CC' AA') :
    QuasiIso (reducedTransformationComplexCompRight v₁ v₂ f) := by
  rw [quasiIso_iff]
  intro q
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, q = p + 1 := ⟨q - 1, by ring⟩
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ⟨injective_homologyMap_reducedTransformationComplexCompRight e he hf v₁ v₂ p,
    surjective_homologyMap_reducedTransformationComplexCompRight e he hf v₁ v₂ p⟩

end ComplexQuasiIso

end AInfinityHom

end TauCeti
