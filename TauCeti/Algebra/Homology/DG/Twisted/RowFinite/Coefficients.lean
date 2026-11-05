/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Complex
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Finsupp
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Basic
public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Row-finite twisted complexes with DG coefficients

A row-finite twisting cocycle on an arbitrary graded basis `P` gives a twisted complex
with coefficients in any DG right module `M`. Its underlying module is `P →₀ M`, not
the unrestricted product. The differential is transported from `M ⊗_A K_m`, using the
free left DG module `K_m` and the balanced tensor differential. Thus square-zero follows
from the tensor construction, rather than a second Maurer–Cartan sign calculation.
A morphism of DG right modules, applied to every coefficient, commutes with these differentials
and so gives a morphism of twisted complexes
(`TauCeti.RowFiniteTwistingCocycle.coefficientCochainComplexMap`); it is a quasi-isomorphism
exactly when every relative cycle of coefficient vectors is a relative boundary.

The characteristic formula on a homogeneous elementary vector is
`D(single x α) = single x (dM α) + (-1)^|α| ∑_y single y (α · m x y)`,
where the sum is over the finite support of the row. The tensor identification preserves
total degree. For finite `P`, the finite-support/function equivalence recovers the existing
finite twisted differential with the same right action and Koszul sign.

These are ordinary tensor products; no semi-free filtration, resolution or derived
comparison is asserted.

The coefficient complex is assembled by `gradedCochainComplex`. Its terms are identified with
the total-degree pieces by `RowFiniteTwistingCocycle.coefficientCochainComplexXEquiv`, and
degree-preserving maps and degree `-1` homotopies of coefficient vectors which are compatible
with the coefficient differentials induce morphisms and homotopies of coefficient complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ}

namespace BalancedTensorProduct

attribute [local instance] tensorGradedRight tensorGradedLeft

local notation "coefficientGrading" => grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
  (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind))

/-- The free-module tensor identification preserves total degree. -/
theorem finsuppScalarRight_mem_rowFiniteTotalGrading {n : ℤ}
    {z : BalancedTensorProduct R A M (P →₀ A)} (hz : z ∈ (coefficientGrading).piece n) :
    finsuppScalarRight R A M P z ∈ rowFiniteTotalGrading ℳ ind n := by
  rw [grading_piece_eq_iSup (𝒜 := 𝒜)] at hz
  refine (iSup_le fun q ↦ Submodule.map₂_le.mpr fun α hα g hg ↦ ?_ :
    _ ≤ (rowFiniteTotalGrading ℳ ind n).comap (finsuppScalarRight R A M P).toLinearMap) hz
  rw [InternalGrading.ofDecomposition_piece] at hα hg
  rw [mem_rowFiniteTotalGrading_iff] at hg
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, mk_apply, mem_rowFiniteTotalGrading_iff]
  intro y
  rw [finsuppScalarRight_tmul_apply]
  have := op_smul_mem_of_mem_graded (hg y) hα
  convert this using 2
  ring

/-- The inverse tensor identification preserves total degree, even for an infinite basis. -/
theorem finsuppScalarRight_symm_mem_grading {n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteTotalGrading ℳ ind n) :
    (finsuppScalarRight R A M P).symm f ∈ (coefficientGrading).piece n := by
  classical
  rw [mem_rowFiniteTotalGrading_iff] at hf
  rw [finsuppScalarRight_symm_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hsingle : Finsupp.single x (1 : A) ∈ rowFiniteTotalGrading 𝒜 ind (-ind x) := by
    rw [mem_rowFiniteTotalGrading_iff]
    intro y
    by_cases hxy : x = y
    · subst y
      simpa using SetLike.one_mem_graded 𝒜
    · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]
  have := tmul_mem_grading (𝒜 := 𝒜) (InternalGrading.ofDecomposition ℳ)
    (InternalGrading.ofDecomposition (rowFiniteTotalGrading 𝒜 ind))
    (by simpa only [InternalGrading.ofDecomposition_piece] using hf x)
    (by simpa only [InternalGrading.ofDecomposition_piece] using hsingle)
  simpa only [add_neg_cancel_right] using this

/-- The tensor grading is exactly the finite-support total grading under `finsuppScalarRight`. -/
theorem map_grading_piece_eq_rowFiniteTotalGrading (n : ℤ) :
    ((coefficientGrading).piece n).map (finsuppScalarRight R A M P).toLinearMap =
      rowFiniteTotalGrading ℳ ind n := by
  ext f
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact finsuppScalarRight_mem_rowFiniteTotalGrading hz
  · intro hf
    exact ⟨_, finsuppScalarRight_symm_mem_grading hf,
      (finsuppScalarRight R A M P).apply_symm_apply f⟩

end BalancedTensorProduct

namespace RowFiniteTwistingCocycle

open BalancedTensorProduct

variable {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)

/-- The row-finite twisted differential with right-module coefficients, transported from
`M ⊗_A K_m` onto finite-support coefficient vectors. -/
def coefficientDifferential : (P →₀ M) →ₗ[R] (P →₀ M) :=
  (finsuppScalarRight R A M P).toLinearMap ∘ₗ
    differential hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA) ∘ₗ
      (finsuppScalarRight R A M P).symm.toLinearMap

/-- The specified tensor identification intertwines the two differentials. -/
@[simp]
theorem coefficientDifferential_finsuppScalarRight (z : BalancedTensorProduct R A M (P →₀ A)) :
    m.coefficientDifferential hM (finsuppScalarRight R A M P z) =
      finsuppScalarRight R A M P
        (differential hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA) z) := by
  simp [coefficientDifferential]

/-- On a homogeneous elementary vector the differential uses only its finite row, with the
right-module action and the Koszul sign of the coefficient. -/
theorem coefficientDifferential_single (x : P) {q : ℤ} {α : M} (hα : α ∈ ℳ q) :
    m.coefficientDifferential hM (Finsupp.single x α) =
      Finsupp.single x (dM α) + q.negOnePow •
        (m.m x).sum (fun y a ↦ Finsupp.single y (op a • α)) := by
  classical
  rw [single_eq_finsuppScalarRight_tmul R A M P x α,
    coefficientDifferential_finsuppScalarRight,
    differential_tmul_of_mem hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA) hα,
    m.differential_single_one hA]
  rw [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  simp

/-- The coefficient differential squares to zero by the balanced tensor differential law. -/
@[simp]
theorem coefficientDifferential_sq_zero (f : P →₀ M) :
    m.coefficientDifferential hM (m.coefficientDifferential hM f) = 0 := by
  simp [coefficientDifferential]

/-- The coefficient differential increases total degree by one. -/
theorem isHomogeneous_coefficientDifferential :
    LinearMap.IsHomogeneous (m.coefficientDifferential hM)
      (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ ind) 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro n f hf
  rw [← (finsuppScalarRight R A M P).apply_symm_apply f,
    coefficientDifferential_finsuppScalarRight]
  exact finsuppScalarRight_mem_rowFiniteTotalGrading
    ((isHomogeneous_differential hM (m.isDGLeftModule_rowFiniteTwistedDifferential hA)).map_mem
      (finsuppScalarRight_symm_mem_grading hf))

/-- The row-finite twisted complex with coefficients in a DG right module, in total
cohomological degree. It has no finiteness restriction on its basis. -/
def coefficientCochainComplex : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteTotalGrading ℳ ind) (m.coefficientDifferential hM)
    (m.isHomogeneous_coefficientDifferential hM) (fun _ f ↦ m.coefficientDifferential_sq_zero hM f)

/-- The terms of the coefficient complex are the finite-support total-degree pieces. -/
@[simp]
theorem coefficientCochainComplex_X (n : ℤ) :
    (m.coefficientCochainComplex hM).X n = ModuleCat.of R (rowFiniteTotalGrading ℳ ind n) := by
  rw [coefficientCochainComplex, gradedCochainComplex_X]

/-- The complex differential is the restriction of the coefficient differential to the
appropriate total-degree pieces. -/
@[simp]
theorem coefficientCochainComplex_d (n : ℤ) :
    (m.coefficientCochainComplex hM).d n (n + 1) =
      eqToHom (m.coefficientCochainComplex_X hM n) ≫
        ModuleCat.ofHom ((m.coefficientDifferential hM).restrict
          (fun _ hf ↦ (m.isHomogeneous_coefficientDifferential hM).map_mem hf)) ≫
        eqToHom (m.coefficientCochainComplex_X hM (n + 1)).symm := by
  unfold coefficientCochainComplex
  rw [gradedCochainComplex_d]

section CoefficientMap

variable {N : Type uM} [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  {dN : N →ₗ[R] N} (hN : IsDGRightModule hA 𝒩 dN)

/-- A morphism of DG right modules, applied to every coefficient, commutes with the coefficient
differentials. -/
theorem coefficientDifferential_mapRange (f : DGRightModuleHom hM hN) (g : P →₀ M) :
    m.coefficientDifferential hN
        (Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g) =
      Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R)
        (m.coefficientDifferential hM g) := by
  classical
  have hF (y : P) (β : M) : Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R)
      (Finsupp.single y β) = Finsupp.single y (f β) := by
    simp
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' hg hg' => simp only [map_add, hg, hg']
  | single x α =>
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous q α =>
      have hfα : f α ∈ 𝒩 q := f.map_mem' α.2
      rw [hF, m.coefficientDifferential_single hN x hfα,
        m.coefficientDifferential_single hM x α.2, map_add, hF, Units.smul_def, Units.smul_def,
        map_zsmul, Finsupp.sum, Finsupp.sum, map_sum]
      simp only [hF, map_smul, DGRightModuleHom.map_d]
    | add α β hα hβ => simp only [Finsupp.single_add, map_add, hα, hβ]

variable {hM hN} in
/-- A morphism of DG right modules, applied to every coefficient, preserves total degree. -/
theorem _root_.TauCeti.DGRightModuleHom.mapRange_mem_rowFiniteTotalGrading
    (f : DGRightModuleHom hM hN) {n : ℤ} {g : P →₀ M}
    (hg : g ∈ rowFiniteTotalGrading ℳ ind n) :
    Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g ∈
      rowFiniteTotalGrading 𝒩 ind n := by
  rw [mem_rowFiniteTotalGrading_iff] at hg ⊢
  intro x
  simpa using f.map_mem' (hg x)

variable {hM hN} in
/-- A morphism of DG right modules, applied to every coefficient, is homogeneous of degree zero
for the total gradings. -/
theorem _root_.TauCeti.DGRightModuleHom.isHomogeneous_mapRange (f : DGRightModuleHom hM hN) :
    LinearMap.IsHomogeneous (Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R))
      (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading 𝒩 ind) 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hg ↦ by
    simpa only [add_zero] using f.mapRange_mem_rowFiniteTotalGrading hg

/-- A morphism of DG right modules, applied to every coefficient, as a morphism of the row-finite
twisted complexes with these coefficients. -/
def coefficientCochainComplexMap (f : DGRightModuleHom hM hN) :
    m.coefficientCochainComplex hM ⟶ m.coefficientCochainComplex hN :=
  gradedCochainComplexHom (Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R))
    (f.isHomogeneous_mapRange (ind := ind))
    (LinearMap.ext fun g ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      exact m.coefficientDifferential_mapRange hM hN f g)

/-- In the identifications of the complex terms with the total-degree pieces, the coefficient map
applies `f` to every coefficient. -/
@[simp]
theorem coefficientCochainComplexMap_f_apply (f : DGRightModuleHom hM hN) (n : ℤ)
    (g : rowFiniteTotalGrading ℳ ind n) :
    (eqToHom (m.coefficientCochainComplex_X hN n)
      ((m.coefficientCochainComplexMap hM hN f).f n
        (eqToHom (m.coefficientCochainComplex_X hM n).symm g)) : P →₀ N) =
      Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g := by
  unfold coefficientCochainComplexMap coefficientCochainComplex
  exact gradedCochainComplexHom_f_apply _ _ _ n g

/-- The identity morphism of DG right modules gives the identity coefficient map. -/
@[simp]
theorem coefficientCochainComplexMap_id :
    m.coefficientCochainComplexMap hM hM (DGRightModuleHom.id hM) = 𝟙 _ := by
  unfold coefficientCochainComplexMap coefficientCochainComplex
  rw [← gradedCochainComplexHom_id]
  congr 1
  ext
  simp

/-- Coefficient maps preserve composition of morphisms of DG right modules.

The simp rule combines composites of coefficient maps into the coefficient map of the composite
morphism of DG right modules. -/
@[simp ←]
theorem coefficientCochainComplexMap_comp {Q : Type uM} [AddCommGroup Q] [Module R Q]
    [Module Aᵐᵒᵖ Q] [IsScalarTower R Aᵐᵒᵖ Q] {𝒬 : ℤ → Submodule R Q} [DirectSum.Decomposition 𝒬]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒬]
    {dQ : Q →ₗ[R] Q} (hQ : IsDGRightModule hA 𝒬 dQ)
    (f : DGRightModuleHom hM hN) (g : DGRightModuleHom hN hQ) :
    m.coefficientCochainComplexMap hM hQ (g.comp f) =
      m.coefficientCochainComplexMap hM hN f ≫ m.coefficientCochainComplexMap hN hQ g := by
  unfold coefficientCochainComplexMap coefficientCochainComplex
  rw [← gradedCochainComplexHom_comp]
  congr 1
  ext
  simp

/-- **Quasi-isomorphisms of coefficient maps, on elements.** The coefficient map of `f` is a
quasi-isomorphism exactly when every relative cycle `(g, k)` of coefficient vectors, with
`D g = 0` and `f g = D k`, is a relative boundary `(D u, f u + D v)` in the matching degrees. -/
theorem quasiIso_coefficientCochainComplexMap_iff (f : DGRightModuleHom hM hN) :
    QuasiIso (m.coefficientCochainComplexMap hM hN f) ↔
      ∀ n (g : P →₀ M) (k : P →₀ N), g ∈ rowFiniteTotalGrading ℳ ind (n + 1) →
        k ∈ rowFiniteTotalGrading 𝒩 ind n → m.coefficientDifferential hM g = 0 →
        Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
          m.coefficientDifferential hN k →
        ∃ u ∈ rowFiniteTotalGrading ℳ ind n, ∃ v ∈ rowFiniteTotalGrading 𝒩 ind (n - 1),
          m.coefficientDifferential hM u = g ∧
            Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u +
              m.coefficientDifferential hN v = k :=
  quasiIso_gradedCochainComplexHom_iff _ _ _

end CoefficientMap

/-- For finite `P`, the finite-support/function equivalence intertwines the coefficient
differential with the original finite twisted differential. -/
theorem linearEquivFunOnFinite_coefficientDifferential [Fintype P] (f : P →₀ M) :
    Finsupp.linearEquivFunOnFinite R M P (m.coefficientDifferential hM f) =
      twistedDifferential (fun x y ↦ m.m x y) ℳ dM
        (Finsupp.linearEquivFunOnFinite R M P f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x α =>
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous q α =>
      rw [m.coefficientDifferential_single hM x α.2, Finsupp.linearEquivFunOnFinite_single,
        twistedDifferential_single (fun x y ↦ m.m x y) dM x α.2]
      ext y
      simp [Finsupp.single_apply, Pi.single_apply, Finsupp.sum_fintype, eq_comm]
    | add α β hα hβ => simp only [Finsupp.single_add, map_add, hα, hβ]

/-! ### Morphisms and homotopies of coefficient complexes -/

/-- The degree-`n` term of the coefficient complex is the finite-support total-degree piece. -/
def coefficientCochainComplexXEquiv (n : ℤ) :
    (m.coefficientCochainComplex hM).X n ≃ₗ[R] rowFiniteTotalGrading ℳ ind n :=
  gradedCochainComplexXEquiv n

/-- Under `coefficientCochainComplexXEquiv`, the complex differential is the coefficient
differential. -/
theorem coefficientCochainComplexXEquiv_d (n : ℤ) (x : (m.coefficientCochainComplex hM).X n) :
    (m.coefficientCochainComplexXEquiv hM (n + 1)
        (((m.coefficientCochainComplex hM).d n (n + 1)).hom x) : P →₀ M) =
      m.coefficientDifferential hM (m.coefficientCochainComplexXEquiv hM n x) :=
  gradedCochainComplexXEquiv_d n x

variable {Q : Type uP} {indQ : Q → ℤ} {m} {mQ : RowFiniteTwistingCocycle 𝒜 dA Q indQ}

/-- A degree-preserving map of coefficient vectors which commutes with the coefficient
differentials, as a morphism of coefficient complexes. -/
def coefficientCochainComplexHom (Φ : (P →₀ M) →ₗ[R] (Q →₀ M))
    (hΦ : LinearMap.IsHomogeneous Φ (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ) 0)
    (hcomm : mQ.coefficientDifferential hM ∘ₗ Φ = Φ ∘ₗ m.coefficientDifferential hM) :
    m.coefficientCochainComplex hM ⟶ mQ.coefficientCochainComplex hM :=
  gradedCochainComplexHom Φ hΦ hcomm

/-- The components of the morphism of a linear map are that linear map. -/
@[simp]
theorem coefficientCochainComplexXEquiv_coefficientCochainComplexHom_f_apply
    (Φ : (P →₀ M) →ₗ[R] (Q →₀ M))
    (hΦ : LinearMap.IsHomogeneous Φ (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ) 0)
    (hcomm : mQ.coefficientDifferential hM ∘ₗ Φ = Φ ∘ₗ m.coefficientDifferential hM) (n : ℤ)
    (x : (m.coefficientCochainComplex hM).X n) :
    (mQ.coefficientCochainComplexXEquiv hM n
        (((coefficientCochainComplexHom hM Φ hΦ hcomm).f n).hom x) : Q →₀ M) =
      Φ (m.coefficientCochainComplexXEquiv hM n x) :=
  gradedCochainComplexXEquiv_gradedCochainComplexHom_f_apply Φ hΦ hcomm n x

/-- Two morphisms of coefficient complexes agree when their components agree on coefficient
vectors. -/
theorem coefficientCochainComplex_hom_ext
    {φ ψ : m.coefficientCochainComplex hM ⟶ mQ.coefficientCochainComplex hM}
    (h : ∀ n (x : (m.coefficientCochainComplex hM).X n),
      (mQ.coefficientCochainComplexXEquiv hM n ((φ.f n).hom x) : Q →₀ M) =
        mQ.coefficientCochainComplexXEquiv hM n ((ψ.f n).hom x)) : φ = ψ :=
  gradedCochainComplex_hom_ext h

/-- A linear map `H` of degree `-1` with `Φ = D ∘ H + H ∘ D + Ψ` is a homotopy between the
morphisms of coefficient complexes of `Φ` and `Ψ`. -/
def coefficientCochainComplexHomotopy {Φ Ψ : (P →₀ M) →ₗ[R] (Q →₀ M)}
    (hΦ : LinearMap.IsHomogeneous Φ (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ) 0)
    (hΨ : LinearMap.IsHomogeneous Ψ (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ) 0)
    (hcommΦ : mQ.coefficientDifferential hM ∘ₗ Φ = Φ ∘ₗ m.coefficientDifferential hM)
    (hcommΨ : mQ.coefficientDifferential hM ∘ₗ Ψ = Ψ ∘ₗ m.coefficientDifferential hM)
    (H : (P →₀ M) →ₗ[R] (Q →₀ M))
    (hH : LinearMap.IsHomogeneous H (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ)
      (-1))
    (hΦΨ : Φ = mQ.coefficientDifferential hM ∘ₗ H + H ∘ₗ m.coefficientDifferential hM + Ψ) :
    Homotopy (coefficientCochainComplexHom hM Φ hΦ hcommΦ)
      (coefficientCochainComplexHom hM Ψ hΨ hcommΨ) :=
  gradedCochainComplexHomotopy hΦ hΨ hcommΦ hcommΨ H hH hΦΨ

/-- The components of the homotopy of a linear map `H` are `H`. -/
theorem coefficientCochainComplexXEquiv_coefficientCochainComplexHomotopy_hom_apply
    {Φ Ψ : (P →₀ M) →ₗ[R] (Q →₀ M)}
    (hΦ : LinearMap.IsHomogeneous Φ (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ) 0)
    (hΨ : LinearMap.IsHomogeneous Ψ (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ) 0)
    (hcommΦ : mQ.coefficientDifferential hM ∘ₗ Φ = Φ ∘ₗ m.coefficientDifferential hM)
    (hcommΨ : mQ.coefficientDifferential hM ∘ₗ Ψ = Ψ ∘ₗ m.coefficientDifferential hM)
    (H : (P →₀ M) →ₗ[R] (Q →₀ M))
    (hH : LinearMap.IsHomogeneous H (rowFiniteTotalGrading ℳ ind) (rowFiniteTotalGrading ℳ indQ)
      (-1))
    (hΦΨ : Φ = mQ.coefficientDifferential hM ∘ₗ H + H ∘ₗ m.coefficientDifferential hM + Ψ)
    (p q : ℤ) (hpq : p + -1 = q) (x : (m.coefficientCochainComplex hM).X p) :
    (mQ.coefficientCochainComplexXEquiv hM q
        (((coefficientCochainComplexHomotopy hM hΦ hΨ hcommΦ hcommΨ H hH hΦΨ).hom p q).hom x) :
        Q →₀ M) =
      H (m.coefficientCochainComplexXEquiv hM p x) :=
  gradedCochainComplexXEquiv_gradedCochainComplexHomotopy_hom_apply hΦ hΨ hcommΦ hcommΨ H hH
    hΦΨ p q hpq x

end RowFiniteTwistingCocycle

end TauCeti
