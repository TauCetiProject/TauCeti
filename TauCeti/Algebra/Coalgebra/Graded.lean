/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv
public import TauCeti.Algebra.Coalgebra.BaseChange
public import TauCeti.Algebra.Module.GradedModule.Dual.TensorProduct
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Graded coalgebras, counit-coproduct degree behavior, and base change

This file develops Frobenius-free homogeneity properties for `ℤ`-graded coalgebras over a
commutative semiring `R`: evenness of counit degree on nontrivial even-supported coalgebras,
counit degree `-d` from coproduct degree `d`, invariance under degree-zero coalgebra equivalences,
and compatibility with tensor products and scalar extension over both trivially graded and
`ℤ`-graded base algebras `S`.

## Main results

* `Coalgebra.exists_eq_neg_two_mul_of_parityGrading_one_eq_bot_of_isHomogeneous_counit`,
  `Coalgebra.isHomogeneous_counit_of_isHomogeneous_comul`.
* `LinearEquiv.isHomogeneous_counit_iff`, `CoalgEquiv.isHomogeneous_counit_iff`,
  `CoalgEquiv.isHomogeneous_comul_iff`.
* `Coalgebra.isHomogeneous_counit_tensorProduct`, `Coalgebra.isHomogeneous_comul_tensorProduct`,
  `Coalgebra.isHomogeneous_counit_baseChange`, `Coalgebra.isHomogeneous_comul_baseChange`,
  `Coalgebra.isHomogeneous_restrictScalars_counit_baseChange`.
-/

public section

noncomputable section

open scoped DirectSum TensorProduct
open TauCeti

/-- On a nontrivial internally `ℤ`-graded coalgebra supported in even degrees, any homogeneous
degree `d` of the counit is even (`d = -2 * c`). -/
theorem Coalgebra.exists_eq_neg_two_mul_of_parityGrading_one_eq_bot_of_isHomogeneous_counit
    {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Nontrivial A] [Module R A]
    (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] [Coalgebra R A]
    (hparity : parityGrading 𝒜 1 = ⊥) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) d) : ∃ c : ℤ, d = -2 * c := by
  by_contra hd
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  let G := InternalGrading.ofDecomposition 𝒜
  have hzero : (Coalgebra.counit (R := R) (A := A)) = 0 := G.linearMap_ext fun p x hx => by
    rw [InternalGrading.ofDecomposition_piece] at hx
    by_cases hp : p + d = 0
    · have hodd : Odd p := Int.not_even_iff_odd.mp fun ⟨c, hc⟩ => hd ⟨c, by omega⟩
      rw [eq_bot_of_parityGrading_one_eq_bot_of_odd hparity hodd, Submodule.mem_bot] at hx
      simp [hx]
    · exact ((mem_trivialGrading_iff R R).mp (hε.map_mem hx)).resolve_left hp
  have h := congrArg (_root_.TensorProduct.lid R A) (Coalgebra.rTensor_counit_comul (R := R) a)
  exact ha (by simpa [hzero] using h.symm)

private theorem rid_lTensor_counitPiece_comul {R A : Type*} [CommSemiring R] [AddCommMonoid A]
    [Module R A] [Coalgebra R A] (G : InternalGrading R A ℤ) {d p : ℤ} {a : A}
    (hΔa : Coalgebra.comul (R := R) a ∈ (G.tensorProduct G).piece (p + d)) (ε₀ : Module.Dual R A)
    (hε₀_eq : ∀ {y : A}, y ∈ G.piece d → ε₀ y = Coalgebra.counit (R := R) y)
    (hε₀_zero : ∀ {r : ℤ} {y : A}, y ∈ G.piece r → r ≠ d → ε₀ y = 0) (ha : a ∈ G.piece p) :
    ((_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε₀.lTensor A)
      (Coalgebra.comul (R := R) a) = a := by
  let ε : Module.Dual R A := Coalgebra.counit
  let g₁ : A ⊗[R] A →ₗ[R] A := (_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε₀.lTensor A
  let proj : A →ₗ[R] A := (G.piece p).subtype ∘ₗ DirectSum.component R ℤ (fun q => G.piece q) p ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap
  let g₂ : A ⊗[R] A →ₗ[R] A := proj ∘ₗ (_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε.lTensor A
  have hle : (G.tensorProduct G).piece (p + d) ≤ LinearMap.eqLocus g₁ g₂ :=
    G.tensorProduct_piece_le G fun q u hu v hv => by
      rw [LinearMap.mem_eqLocus]
      simp only [g₁, g₂, proj, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
        _root_.TensorProduct.rid_tmul, DirectSum.decomposeLinearEquiv_apply,
        ← DirectSum.apply_eq_component, Submodule.coe_subtype]
      by_cases hqp : q = p
      · subst hqp; rw [hε₀_eq (by simpa using hv),
          DirectSum.decompose_of_mem_same G.piece ((G.piece q).smul_mem (ε v) hu)]
      · rw [hε₀_zero hv (by omega), zero_smul,
          DirectSum.decompose_of_mem_ne G.piece ((G.piece q).smul_mem (ε v) hu) hqp]
  refine (LinearMap.mem_eqLocus.mp (hle hΔa)).trans ?_
  simp only [g₂, proj, LinearMap.comp_apply, LinearEquiv.coe_coe, ε,
    Coalgebra.lTensor_counit_comul, _root_.TensorProduct.rid_tmul, one_smul,
    DirectSum.decomposeLinearEquiv_apply, ← DirectSum.apply_eq_component, Submodule.coe_subtype]
  exact DirectSum.decompose_of_mem_same G.piece ha

/-- On any internally `ℤ`-graded coalgebra, if `comul` is homogeneous of degree `d`, then `counit`
is homogeneous of degree `-d`. -/
theorem Coalgebra.isHomogeneous_counit_of_isHomogeneous_comul {R A : Type*} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [Coalgebra R A] (G : InternalGrading R A ℤ) {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) G.piece
      (G.tensorProduct G).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) G.piece
      (trivialGrading R R) (-d) := by
  set ε : Module.Dual R A := Coalgebra.counit with hε_def
  let ε₀sub : G.dualPiece (-d) := (G.dualPieceEquiv (-d)).symm (ε ∘ₗ (G.piece (- -d)).subtype)
  let ε₀ : Module.Dual R A := ε₀sub
  have hε₀_eq {y : A} (hy : y ∈ G.piece d) : ε₀ y = ε y := by
    simpa [ε₀, ε₀sub] using G.dualPieceEquiv_symm_apply_coe (-d)
      (ε ∘ₗ (G.piece (- -d)).subtype) ⟨y, by simpa using hy⟩
  have hε₀_zero {r : ℤ} {y : A} (hy : y ∈ G.piece r) (hr : r ≠ d) : ε₀ y = 0 :=
    (G.mem_dualPiece_iff (-d) ε₀).mp ε₀sub.2 r y hy (by omega)
  set g₁ : A ⊗[R] A →ₗ[R] A := (_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε₀.lTensor A
    with hg₁_def
  have hconv : ε ∘ₗ g₁ = ε₀ ∘ₗ (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ ε.rTensor A :=
    TensorProduct.ext' fun _ _ => by simp [hg₁_def, mul_comm]
  have hε_eq : ε = ε₀ := G.linearMap_ext fun p a ha => by
    have hc := LinearMap.congr_fun hconv (Coalgebra.comul (R := R) a)
    have hg₁a : g₁ (Coalgebra.comul (R := R) a) = a :=
      rid_lTensor_counitPiece_comul G (hΔ.map_mem ha) ε₀ hε₀_eq hε₀_zero ha
    rw [LinearMap.comp_apply, hg₁a] at hc
    simpa [hε_def, Coalgebra.rTensor_counit_comul] using hc
  rw [← G.mem_dualPiece_iff_isHomogeneous_trivialGrading, hε_eq]; exact ε₀sub.2

section Equiv

variable {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B)
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- A counit-preserving degree-zero linear equivalence preserves homogeneity of the counit at any
degree `d`. -/
theorem LinearEquiv.isHomogeneous_counit_iff (e : A ≃ₗ[R] B)
    (he_hom : TauCeti.LinearMap.IsHomogeneous e.toLinearMap 𝒜 ℬ 0)
    (he_counit : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := B)) ℬ
        (trivialGrading R R) d := by
  have he_equiv : TauCeti.LinearMap.IsHomogeneous e.toLinearMap
      (InternalGrading.ofDecomposition 𝒜).piece (InternalGrading.ofDecomposition ℬ).piece 0 := by
    simpa using he_hom
  have hsymm : TauCeti.LinearMap.IsHomogeneous e.symm.toLinearMap ℬ 𝒜 0 := by
    simpa using he_equiv.linearEquiv_symm
  simp only [TauCeti.LinearMap.isHomogeneous_def]
  refine ⟨fun hA p b hb => ?_, fun hB p a ha => ?_⟩
  · simpa [← he_counit (e.symm b)] using hA p (e.symm b) (by simpa using hsymm.map_mem hb)
  · simpa [he_counit a] using hB p (e a) (by simpa using he_hom.map_mem ha)

/-- A degree-zero coalgebra equivalence preserves homogeneity of the counit at any degree `d`. -/
theorem CoalgEquiv.isHomogeneous_counit_iff (e : A ≃ₗc[R] B)
    (he_hom : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e) 𝒜 ℬ 0) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := B)) ℬ
        (trivialGrading R R) d := by
  have hcoe : (e : A ≃ₗ[R] B).toLinearMap = LinearMap.ofClass e := by ext; rfl
  exact (e : A ≃ₗ[R] B).isHomogeneous_counit_iff 𝒜 ℬ (hcoe ▸ he_hom)
    (CoalgHomClass.counit_comp_apply e) d

private theorem CoalgEquiv.isHomogeneous_comul_imp (e : A ≃ₗc[R] B)
    (he : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e) 𝒜 ℬ 0)
    (hsymm : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e.symm) ℬ 𝒜 0) {d : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) ℬ
      ((InternalGrading.ofDecomposition ℬ).tensorProduct
        (InternalGrading.ofDecomposition ℬ)).piece d := by
  let GA := InternalGrading.ofDecomposition 𝒜; let GB := InternalGrading.ofDecomposition ℬ
  have he' : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e) GA.piece GB.piece 0 := by
    simpa [GA, GB] using he
  have hsymm' : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e.symm) GB.piece GA.piece 0 := by
    simpa [GA, GB] using hsymm
  have hA' : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) GA.piece
      (GA.tensorProduct GA).piece d := by simpa [GA] using hA
  have hB_eq : Coalgebra.comul (R := R) (A := B) =
      _root_.TensorProduct.map (LinearMap.ofClass e) (LinearMap.ofClass e) ∘ₗ
        Coalgebra.comul (R := R) (A := A) ∘ₗ LinearMap.ofClass e.symm :=
    LinearMap.ext fun _ => by simp [CoalgHomClass.map_comp_comul_apply]
  rw [hB_eq]; simpa [GB] using (he'.tensorProduct he').comp (hA'.comp hsymm')

/-- A degree-zero coalgebra equivalence between internally `ℤ`-graded coalgebras preserves
homogeneity of the coproduct at any degree `d`. -/
theorem CoalgEquiv.isHomogeneous_comul_iff (e : A ≃ₗc[R] B)
    (he_hom : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e) 𝒜 ℬ 0) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) ℬ
        ((InternalGrading.ofDecomposition ℬ).tensorProduct
          (InternalGrading.ofDecomposition ℬ)).piece d := by
  let GA := InternalGrading.ofDecomposition 𝒜; let GB := InternalGrading.ofDecomposition ℬ
  have hcoe : (e : A ≃ₗ[R] B).toLinearMap = LinearMap.ofClass e := by ext; rfl
  have hcoe_symm : (e : A ≃ₗ[R] B).symm.toLinearMap = LinearMap.ofClass e.symm := by ext; rfl
  have hsymm_symm : LinearMap.ofClass e.symm.symm = LinearMap.ofClass e := by ext; rfl
  have hsymm : TauCeti.LinearMap.IsHomogeneous (LinearMap.ofClass e.symm) ℬ 𝒜 0 := by
    have he_GA : TauCeti.LinearMap.IsHomogeneous (e : A ≃ₗ[R] B).toLinearMap GA.piece GB.piece
        0 := by rw [hcoe]; simpa [GA, GB] using he_hom
    rw [← hcoe_symm]; simpa [GA, GB] using he_GA.linearEquiv_symm
  exact ⟨e.isHomogeneous_comul_imp 𝒜 ℬ he_hom hsymm,
    e.symm.isHomogeneous_comul_imp ℬ 𝒜 hsymm (hsymm_symm ▸ he_hom)⟩

end Equiv

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [CoalgebraStruct R A] [CoalgebraStruct R B]
  (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ) {dA dB : ℤ}

/-- On a tensor product `A ⊗[R] B` of internally `ℤ`-graded coalgebras, homogeneous counits of
degrees `dA` and `dB` tensor to a homogeneous counit of degree `dA + dB`. -/
theorem Coalgebra.isHomogeneous_counit_tensorProduct
    (hA : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) GA.piece
      (trivialGrading R R) dA)
    (hB : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := B)) GB.piece
      (trivialGrading R R) dB) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A ⊗[R] B))
      (GA.tensorProduct GB).piece (trivialGrading R R) (dA + dB) := by
  rw [← (GA.tensorProduct GB).mem_dualPiece_iff_isHomogeneous_trivialGrading,
    TensorProduct.counit_eq_dualDistrib]
  exact GA.dualDistrib_tmul_mem_dualPiece GB
    ((GA.mem_dualPiece_iff_isHomogeneous_trivialGrading dA _).mpr hA)
    ((GB.mem_dualPiece_iff_isHomogeneous_trivialGrading dB _).mpr hB)

/-- On a tensor product `A ⊗[R] B` of internally `ℤ`-graded coalgebras, homogeneous coproducts of
degrees `dA` and `dB` tensor to a homogeneous coproduct of degree `dA + dB`. -/
theorem Coalgebra.isHomogeneous_comul_tensorProduct
    (hA : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) GA.piece
      (GA.tensorProduct GA).piece dA)
    (hB : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) GB.piece
      (GB.tensorProduct GB).piece dB) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A ⊗[R] B))
      (GA.tensorProduct GB).piece
      ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece (dA + dB) := by
  have hdef : Coalgebra.comul (R := R) (A := A ⊗[R] B) =
      (TensorProduct.tensorTensorTensorComm R A A B B).toLinearMap ∘ₗ
        _root_.TensorProduct.map (Coalgebra.comul (R := R) (A := A))
          (Coalgebra.comul (R := R) (A := B)) := TensorProduct.ext' fun _ _ => rfl
  rw [hdef]
  simpa using (InternalGrading.isHomogeneous_tensorTensorTensorComm GA GA GB GB).comp
    (hA.tensorProduct hB)

end TensorProduct

section BaseChange

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]

/-- Extending scalars from `R` to a trivially graded commutative `R`-algebra `S` preserves
homogeneity of the counit for `Submodule.baseChange`. -/
theorem Coalgebra.isHomogeneous_counit_baseChange (𝒜 : ℤ → Submodule R A) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := S) (A := S ⊗[R] A))
      (fun i : ℤ => (𝒜 i).baseChange S) (trivialGrading S S) d :=
  TauCeti.LinearMap.isHomogeneous_def.mpr fun p z hz => by
    by_cases hp : p + d = 0
    · simp [hp]
    · have hle : (𝒜 p).baseChange S ≤
          LinearMap.ker (Coalgebra.counit (R := S) (A := S ⊗[R] A)) := by
        rw [Submodule.baseChange_eq_span, Submodule.span_le]; rintro - ⟨a, ha, rfl⟩
        simp [LinearMap.mem_ker, TensorProduct.counit_baseChange_eq_dualBaseChange,
          ((mem_trivialGrading_iff R R).mp (hε.map_mem ha)).resolve_left hp]
      exact (mem_trivialGrading_iff S S).mpr (Or.inr (LinearMap.mem_ker.mp (hle hz)))

/-- Extending scalars of an internally `ℤ`-graded `R`-coalgebra `A` from `R` to a trivially graded
commutative `R`-algebra `S` preserves homogeneity of the coproduct for `Submodule.baseChange`. -/
theorem Coalgebra.isHomogeneous_comul_baseChange (𝒜 : ℤ → Submodule R A)
    [DirectSum.Decomposition 𝒜] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := S) (A := S ⊗[R] A))
      (fun i : ℤ => (𝒜 i).baseChange S)
      ((InternalGrading.ofDecomposition (fun i : ℤ => (𝒜 i).baseChange S)).tensorProduct
        (InternalGrading.ofDecomposition (fun i : ℤ => (𝒜 i).baseChange S))).piece d := by
  let GA := InternalGrading.ofDecomposition 𝒜
  let GSA := InternalGrading.ofDecomposition (fun i : ℤ => (𝒜 i).baseChange S)
  let φ : A ⊗[R] A →ₗ[R] (S ⊗[R] A) ⊗[S] (S ⊗[R] A) :=
    ((_root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A
      A).toLinearMap.restrictScalars R) ∘ₗ
      _root_.TensorProduct.mk R (S ⊗[S] S) (A ⊗[R] A) ((1 : S) ⊗ₜ[S] (1 : S))
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun n z hz => ?_
  let target := (GSA.tensorProduct GSA).piece (n + d)
  suffices hle : (𝒜 n).baseChange S ≤ target.comap (Coalgebra.comul (R := S) (A := S ⊗[R] A)) from
    Submodule.mem_comap.mp (hle hz)
  rw [Submodule.baseChange_eq_span, Submodule.span_le]; rintro - ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, _root_.TensorProduct.mk_apply,
    TensorProduct.comul_tmul, CommSemiring.comul_apply]
  refine GA.tensorProduct_piece_le GA (C := (target.restrictScalars R).comap φ)
    (fun p a₁ ha₁ a₂ ha₂ => ?_) (hΔ.map_mem ha)
  rw [InternalGrading.ofDecomposition_piece] at ha₁ ha₂
  have h1 : (1 : S) ⊗ₜ[R] a₁ ∈ GSA.piece p := by
    simpa [GSA] using Submodule.tmul_mem_baseChange_of_mem (1 : S) ha₁
  have h2 : (1 : S) ⊗ₜ[R] a₂ ∈ GSA.piece (n + d - p) := by
    simpa [GSA] using Submodule.tmul_mem_baseChange_of_mem (1 : S) ha₂
  simpa [φ, target] using GSA.tmul_mem_tensorProduct GSA h1 h2

/-- Extending scalars along a `ℤ`-graded commutative `R`-algebra `S`: if the counit of `A` has
degree `d` into `trivialGrading R R`, then the `S`-linear counit of `S ⊗[R] A` viewed over `R` is
homogeneous of degree `d` from the total-degree grading of `S ⊗[R] A` into `𝒮`. -/
theorem Coalgebra.isHomogeneous_restrictScalars_counit_baseChange
    (𝒮 : ℤ → Submodule R S) [DirectSum.Decomposition 𝒮]
    (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) d) :
    TauCeti.LinearMap.IsHomogeneous
      ((Coalgebra.counit (R := S) (A := S ⊗[R] A)).restrictScalars R)
      ((InternalGrading.ofDecomposition 𝒮).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece 𝒮 d := by
  let GS := InternalGrading.ofDecomposition 𝒮; let GA := InternalGrading.ofDecomposition 𝒜
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun n z hz =>
    GS.tensorProduct_piece_le GA
      (C := (𝒮 (n + d)).comap ((Coalgebra.counit (R := S) (A := S ⊗[R] A)).restrictScalars R))
      (fun p s hs a ha => ?_) hz
  rw [InternalGrading.ofDecomposition_piece] at hs ha
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
    TensorProduct.counit_baseChange_eq_dualBaseChange, Module.Dual.baseChange_apply_tmul]
  by_cases hqd : n - p + d = 0
  · have hdeg : n + d = p := by omega
    exact hdeg ▸ (𝒮 p).smul_mem (Coalgebra.counit (R := R) a) hs
  · simp [((mem_trivialGrading_iff R R).mp (hε.map_mem ha)).resolve_left hqd]

end BaseChange
