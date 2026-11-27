/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.LinearAlgebra.Matrix.TensorProduct
public import TauCeti.LinearAlgebra.Matrix.Trace.Partial
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.Topology.Algebra.IsOpenUnits
public import TauCeti.Topology.PiCurry
import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo

/-!
# Topological properties of matrices

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.

Matrices with countably many rows and columns are second countable when their entries are, and
matrices with finitely many rows and columns are σ-compact, respectively locally compact, when
their entries are. Matrices over a compact space are compact.

Square matrices act jointly continuously on column vectors by `Matrix.mulVec`, the action of
`Mathlib.LinearAlgebra.Matrix.Action`; through the unit group, so does `GL n R`
(`Units.continuousSMul`).

The same product topology gives entrywise control of a real matrix-valued map near a point of
continuity, again without a matrix norm
(`ContinuousAt.exists_ball_subset_forall_abs_sub_le`), and the product uniformity gives the
uniform version for uniformly continuous maps (`UniformContinuous.exists_pos_forall_abs_sub_le`).

Over a topological field, the inverse of a matrix-valued function that is continuous at a point
with invertible value is continuous there (`ContinuousAt.matrix_inv`), and so are its entries
(`ContinuousAt.matrix_inv_apply`).

Square matrices over a commutative topological ring `R` with open units again have open units
(`Matrix.instIsOpenUnits`). The invertible matrices are the preimage of the open set of units of
`R` under the continuous determinant, and the inverse `A⁻¹ = (det A)⁻¹ • adj A` is continuous on
them because the inverse of the determinant is. Over a nonarchimedean local field `E`, which has
open units because it is a Hausdorff topological field, this says that `GL_n(E)` with the
topology of the unit group is the open subspace `{det ≠ 0}` of the matrices `M_n(E)`. The
hypothesis on `R` cannot be dropped: over the adeles, inversion is not continuous on the units
for the subspace topology, already for `n = 1`.

Each characteristic coefficient is continuous over a commutative topological ring
(`Matrix.continuous_charpoly_coeff`). The proof uses Mathlib's universal characteristic polynomial
`Matrix.charpoly.univ`, whose coefficients are multivariate polynomials in the matrix entries;
so is each coefficient of the reversed characteristic polynomial `det (1 - X A)`
(`Matrix.continuous_charpolyRev_coeff`).
Hence two continuous maps `ρ ρ' : Γ → Mₙ(A)` into a Hausdorff topological ring whose
characteristic polynomials agree on a dense subset of `Γ` have the same characteristic polynomial
everywhere (`Matrix.charpoly_eq_of_dense`). In size two the characteristic polynomial is
determined by the trace and the determinant (`Matrix.charpoly_eq_charpoly_iff_fin_two`), so for
maps `ρ ρ' : Γ → M₂(A)`, such as continuous representations `Γ → GL₂(A)` composed with
`Units.val`, it suffices that the traces and determinants agree on the dense subset
(`Matrix.charpoly_eq_of_dense_fin_two`).

The Kronecker product of two continuously varying matrices is continuous in the product topology.
In particular the ⋆-algebra homomorphisms `A ↦ A ⊗ₖ 1` and `B ↦ 1 ⊗ₖ B` are continuous. So are
both partial traces of a continuously varying matrix on a product index.

A matrix-valued function converges exactly when each of its entries does
(`Matrix.tendsto_iff_tendsto_apply`), and exactly when its products with all column vectors do
(`Matrix.tendsto_iff_forall_tendsto_mulVec`). In particular, pointwise convergence of
sesquilinear forms gives convergence of their Gram matrices in any pair of finite bases
(`LinearMap.tendsto_toMatrix₂`). Square matrices tending to the identity are eventually invertible
(`Matrix.eventually_det_ne_zero_of_tendsto_one`). The matrices with nonnegative diagonal form a
closed set (`Matrix.isClosed_setOfPred_nonneg_diag`).

The matrices whose entries all lie in a dense set are dense (`Dense.matrix`), the dense
counterpart of Mathlib's `IsOpen.matrix`.

`Matrix.ofHomeomorph` bundles `Matrix.of` as a homeomorphism `(m → n → α) ≃ₜ Matrix m n α`.
Flattening a family of matrices `(i : ι) → Matrix (κ i) (μ i) α` to `(Σ i, κ i × μ i) → α` is a
homeomorphism for the entrywise product topologies (`TauCeti.piMatrixHomeomorph`), matching
`TauCeti.piMatrixLinearEquiv` as a bijection and yielding continuity of `piMatrixLinearEquiv` and
its inverse.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §3, pp. 3–4.
-/

public section

namespace TauCeti

/-- A space of matrices with finitely many rows and columns over a pseudo-metrizable space is
pseudo-metrizable. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

/-- Matrices with countably many rows and columns over a second-countable space are
second countable. -/
instance {m n α : Type*} [Countable m] [Countable n] [TopologicalSpace α]
    [SecondCountableTopology α] : SecondCountableTopology (Matrix m n α) :=
  inferInstanceAs (SecondCountableTopology (m → n → α))

/-- Matrices with finitely many rows and columns over a σ-compact space form a σ-compact space. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α] [SigmaCompactSpace α] :
    SigmaCompactSpace (Matrix m n α) :=
  inferInstanceAs (SigmaCompactSpace (m → n → α))

/-- Matrices with finitely many rows and columns over a locally compact space form a locally
compact space. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α] [LocallyCompactSpace α] :
    LocallyCompactSpace (Matrix m n α) :=
  inferInstanceAs (LocallyCompactSpace (m → n → α))

/-- Matrices over a compact space form a compact space (Tychonoff). -/
instance {m n α : Type*} [TopologicalSpace α] [CompactSpace α] :
    CompactSpace (Matrix m n α) :=
  inferInstanceAs (CompactSpace (m → n → α))

/-- Square matrices act jointly continuously on column vectors by `Matrix.mulVec`. -/
instance {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousMul R] : ContinuousSMul (Matrix n n R) (n → R) :=
  ⟨continuous_fst.matrix_mulVec continuous_snd⟩

end TauCeti

namespace Matrix

/-- `Matrix.of` bundled as a homeomorphism between curried functions `m → n → α` and matrices
`Matrix m n α` with the entrywise product topology. -/
def ofHomeomorph {m n α : Type*} [TopologicalSpace α] : (m → n → α) ≃ₜ Matrix m n α where
  toEquiv := of
  continuous_toFun := continuous_id.matrixOf
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_id.matrix_elem i j

@[simp]
theorem ofHomeomorph_toEquiv {m n α : Type*} [TopologicalSpace α] :
    (ofHomeomorph : (m → n → α) ≃ₜ Matrix m n α).toEquiv = of := (rfl)

@[simp]
theorem ofHomeomorph_apply {m n α : Type*} [TopologicalSpace α] (f : m → n → α) :
    ofHomeomorph f = of f := (rfl)

@[simp]
theorem ofHomeomorph_symm_apply {m n α : Type*} [TopologicalSpace α] (A : Matrix m n α) :
    ofHomeomorph.symm A = of.symm A := (rfl)

end Matrix

namespace TauCeti

section MatrixCoordinates

variable {ι : Type*} (κ μ : ι → Type*) (α : Type*) [TopologicalSpace α]

/-- Flatten a family of matrices `(i : ι) → Matrix (κ i) (μ i) α` to a single coordinate tuple
indexed by `Σ i, κ i × μ i`, as a homeomorphism for the entrywise product topologies. -/
def piMatrixHomeomorph :
    ((i : ι) → Matrix (κ i) (μ i) α) ≃ₜ ((p : Σ i, κ i × μ i) → α) :=
  (Homeomorph.piCongrRight fun _ ↦
      Matrix.ofHomeomorph.symm.trans Homeomorph.piCurry.symm).trans
    (piCurryHomeomorph fun (_ : ι) (_ : κ _ × μ _) ↦ α).symm

@[simp]
theorem piMatrixHomeomorph_apply (A : (i : ι) → Matrix (κ i) (μ i) α) (p : Σ i, κ i × μ i) :
    piMatrixHomeomorph κ μ α A p = A p.1 p.2.1 p.2.2 := by
  simp [piMatrixHomeomorph, Function.uncurry]

@[simp]
theorem piMatrixHomeomorph_symm_apply (a : (p : Σ i, κ i × μ i) → α) (i : ι) (j : κ i) (k : μ i) :
    (piMatrixHomeomorph κ μ α).symm a i j k = a ⟨i, j, k⟩ := by
  simp [piMatrixHomeomorph, Function.curry]

/-- As an underlying equivalence, `TauCeti.piMatrixHomeomorph` agrees with
`TauCeti.piMatrixLinearEquiv`. -/
theorem piMatrixHomeomorph_toEquiv (R : Type*) [Semiring R] [AddCommMonoid α] [Module R α] :
    (piMatrixHomeomorph κ μ α).toEquiv = (piMatrixLinearEquiv R κ μ α).toEquiv := by
  ext A p; simp

/-- The forward map of `TauCeti.piMatrixHomeomorph` agrees with `TauCeti.piMatrixLinearEquiv`. -/
theorem coe_piMatrixHomeomorph_eq_piMatrixLinearEquiv (R : Type*) [Semiring R]
    [AddCommMonoid α] [Module R α] :
    ⇑(piMatrixHomeomorph κ μ α) = ⇑(piMatrixLinearEquiv R κ μ α) := by
  ext A p; simp

/-- The inverse map of `TauCeti.piMatrixHomeomorph` agrees with the inverse of
`TauCeti.piMatrixLinearEquiv`. -/
theorem coe_piMatrixHomeomorph_symm_eq_piMatrixLinearEquiv_symm (R : Type*) [Semiring R]
    [AddCommMonoid α] [Module R α] :
    ⇑(piMatrixHomeomorph κ μ α).symm = ⇑(piMatrixLinearEquiv R κ μ α).symm := by
  ext a i j k; simp

variable {κ μ α}

/-- The linear equivalence `TauCeti.piMatrixLinearEquiv` is continuous for the entrywise product
topologies. -/
@[continuity, fun_prop]
theorem continuous_piMatrixLinearEquiv {R : Type*} [Semiring R] [AddCommMonoid α] [Module R α] :
    Continuous (piMatrixLinearEquiv R κ μ α) :=
  coe_piMatrixHomeomorph_eq_piMatrixLinearEquiv κ μ α R ▸ (piMatrixHomeomorph κ μ α).continuous

/-- The inverse of `TauCeti.piMatrixLinearEquiv` is continuous for the entrywise product
topologies. -/
@[continuity, fun_prop]
theorem continuous_piMatrixLinearEquiv_symm {R : Type*} [Semiring R]
    [AddCommMonoid α] [Module R α] : Continuous (piMatrixLinearEquiv R κ μ α).symm :=
  coe_piMatrixHomeomorph_symm_eq_piMatrixLinearEquiv_symm κ μ α R ▸
    (piMatrixHomeomorph κ μ α).symm.continuous

end MatrixCoordinates

end TauCeti

namespace ContinuousAt

open Filter Metric
open scoped Topology

/-- If a real matrix-valued map `a` on a pseudo-metric space is continuous at `x`, then for every
neighbourhood `s` of `x` and every `ε > 0` there is a ball `B(x, r) ⊆ s` on which every entry of
`a` differs from its value at `x` by at most `ε`. -/
theorem exists_ball_subset_forall_abs_sub_le {X m n : Type*} [PseudoMetricSpace X] [Finite m]
    [Finite n] {a : X → Matrix m n ℝ} {x : X} (hcont : ContinuousAt a x) {s : Set X}
    (hs : s ∈ 𝓝 x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ s ∧ ∀ y ∈ ball x r, ∀ i j, |a y i j - a x i j| ≤ ε := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ s ∧ ∀ i j, |a y i j - a x i j| ≤ ε := by
    refine Eventually.and hs (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    have hij : ContinuousAt (fun y => a y i j) x :=
      (continuous_id.matrix_elem i j).continuousAt.comp hcont
    filter_upwards [Metric.tendsto_nhds.1 hij ε hε] with y hy
    exact (Real.dist_eq _ _ ▸ hy).le
  obtain ⟨r, hr, hrx⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨r, hr, fun y hy => (hrx y hy).1, fun y hy => (hrx y hy).2⟩

end ContinuousAt

namespace UniformContinuous

open Filter Metric
open scoped Uniformity

/-- If a real matrix-valued map `a` on a pseudo-metric space is uniformly continuous, then for every
`ε > 0` there is `r > 0` such that every entry of `a` varies by at most `ε` between any two points
at distance less than `r`. -/
theorem exists_pos_forall_abs_sub_le {X m n : Type*} [PseudoMetricSpace X] [Finite m] [Finite n]
    {a : X → Matrix m n ℝ} (ha : UniformContinuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y, dist x y < r → ∀ i j, |a x i j - a y i j| ≤ ε := by
  have hev : ∀ᶠ z : X × X in 𝓤 X, ∀ i j, |a z.1 i j - a z.2 i j| ≤ ε := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hij : UniformContinuous fun x => a x i j := (Matrix.uniformContinuous _ _ _).1 ha i j
    filter_upwards [hij (dist_mem_uniformity hε)] with z hz
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Real.dist_eq] at hz
    exact hz.le
  obtain ⟨r, hr, hrz⟩ := uniformity_basis_dist.mem_iff.1 hev
  exact ⟨r, hr, fun x y hxy => @hrz (x, y) hxy⟩

end UniformContinuous

section Inverse

variable {X n K : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] {A : X → Matrix n n K} {x : X}

/-- The inverse of a matrix-valued function is continuous at every point where the function is
continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) :
    ContinuousAt (fun y ↦ (A y)⁻¹) x :=
  (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)).comp hA

/-- The entries of the inverse of a matrix-valued function are continuous at every point where the
function is continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv_apply (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) (k l : n) :
    ContinuousAt (fun y ↦ (A y)⁻¹ k l) x :=
  (continuous_apply_apply k l).continuousAt.comp (hA.matrix_inv hdet)

end Inverse

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

/-- Every characteristic coefficient is continuous for the entrywise matrix topology. -/
@[continuity, fun_prop]
theorem continuous_charpoly_coeff (k : ℕ) :
    Continuous (fun A : Matrix n n R => A.charpoly.coeff k) := by
  have h : Continuous (fun A : Matrix n n R =>
      MvPolynomial.eval (Function.uncurry A) ((charpoly.univ R n).coeff k)) :=
    (MvPolynomial.continuous_eval (p := (charpoly.univ R n).coeff k)).comp
      (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)
  have hmatrix (A : Matrix n n R) : of (Function.curry (Function.uncurry A)) = A := by
    ext i j
    rfl
  simpa only [MvPolynomial.eval, charpoly.univ_coeff_eval₂Hom, hmatrix] using h

/-- Every coefficient of the reversed characteristic polynomial `det (1 - X A)` is continuous for
the entrywise matrix topology. -/
@[continuity, fun_prop]
theorem continuous_charpolyRev_coeff (k : ℕ) :
    Continuous (fun A : Matrix n n R => A.charpolyRev.coeff k) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  simp_rw [← reverse_charpoly, Polynomial.coeff_reverse, charpoly_natDegree_eq_dim]
  exact continuous_charpoly_coeff _

/-- **Recognition on a dense subset.** Two continuous matrix-valued maps `ρ ρ' : Γ → Mₙ(A)` into a
Hausdorff topological ring whose characteristic polynomials agree on a dense subset of `Γ` have
the same characteristic polynomial at every point. -/
theorem charpoly_eq_of_dense [T2Space R] {Γ : Type*} [TopologicalSpace Γ]
    {ρ ρ' : Γ → Matrix n n R} (hρ : Continuous ρ) (hρ' : Continuous ρ') {S : Set Γ}
    (hS : Dense S) (h : ∀ g ∈ S, (ρ g).charpoly = (ρ' g).charpoly) (g : Γ) :
    (ρ g).charpoly = (ρ' g).charpoly := by
  ext k
  exact congrFun (((continuous_charpoly_coeff k).comp hρ).ext_on hS
    ((continuous_charpoly_coeff k).comp hρ') fun x hx ↦ by simp [h x hx]) g

/-- **Recognition on a dense subset in rank two.** Two continuous maps `ρ ρ' : Γ → M₂(A)` into a
Hausdorff topological ring, such as continuous representations into `GL₂(A)` composed with
`Units.val`, whose traces and determinants agree on a dense subset of `Γ` have the same
characteristic polynomial at every point. -/
theorem charpoly_eq_of_dense_fin_two [T2Space R] {Γ : Type*} [TopologicalSpace Γ]
    {ρ ρ' : Γ → Matrix (Fin 2) (Fin 2) R} (hρ : Continuous ρ) (hρ' : Continuous ρ') {S : Set Γ}
    (hS : Dense S) (htr : ∀ g ∈ S, (ρ g).trace = (ρ' g).trace)
    (hdet : ∀ g ∈ S, (ρ g).det = (ρ' g).det) (g : Γ) :
    (ρ g).charpoly = (ρ' g).charpoly :=
  charpoly_eq_of_dense hρ hρ' hS
    (fun x hx ↦ (charpoly_eq_charpoly_iff_fin_two _ _).2 ⟨htr x hx, hdet x hx⟩) g

variable [IsOpenUnits R]

/-- Square matrices over a commutative topological ring with open units have open units: the
invertible matrices form an open set on which inversion is continuous. -/
instance instIsOpenUnits : IsOpenUnits (Matrix n n R) where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val_mk' (f := Inv.inv) (fun A hA ↦ ?_)
      fun u ↦ (coe_units_inv u).symm, ?_⟩
    · obtain ⟨u, hu⟩ := (isUnit_iff_isUnit_det A).1 hA
      exact (continuousAt_matrix_inv A
        (hu ▸ IsOpenUnits.continuousAt_ringInverse u)).continuousWithinAt
    · have hrange : Set.range (Units.val : (Matrix n n R)ˣ → Matrix n n R) =
          det ⁻¹' Set.range (Units.val : Rˣ → R) := by
        ext A
        exact isUnit_iff_isUnit_det A
      rw [hrange]
      exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage continuous_id.matrix_det

end Matrix

open scoped Kronecker

/-- The Kronecker product of two continuous matrix-valued functions is continuous. -/
@[continuity, fun_prop]
theorem Continuous.matrix_kronecker {X R l m n p : Type*} [TopologicalSpace X]
    [TopologicalSpace R] [Mul R] [ContinuousMul R]
    {A : X → Matrix l m R} {B : X → Matrix n p R}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x ↦ A x ⊗ₖ B x) := by
  apply continuous_matrix
  intro i j
  simp only [Matrix.kroneckerMap_apply]
  exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)

section PartialTrace

variable {X R m n : Type*} [TopologicalSpace X] [TopologicalSpace R] [AddCommMonoid R]
  [ContinuousAdd R] {A : X → Matrix (m × n) (m × n) R}

/-- The partial trace over the second factor of a continuous matrix-valued function is
continuous. -/
@[continuity, fun_prop]
theorem Continuous.matrix_partialTraceRight [Fintype n] (hA : Continuous A) :
    Continuous fun x ↦ (A x).partialTraceRight :=
  continuous_matrix fun i j ↦ by
    simpa only [Matrix.partialTraceRight_apply] using
      continuous_finsetSum _ fun k _ ↦ hA.matrix_elem (i, k) (j, k)

/-- The partial trace over the first factor of a continuous matrix-valued function is
continuous. -/
@[continuity, fun_prop]
theorem Continuous.matrix_partialTraceLeft [Fintype m] (hA : Continuous A) :
    Continuous fun x ↦ (A x).partialTraceLeft :=
  continuous_matrix fun i j ↦ by
    simpa only [Matrix.partialTraceLeft_apply] using
      continuous_finsetSum _ fun k _ ↦ hA.matrix_elem (k, i) (k, j)

end PartialTrace

namespace Matrix

variable {R α m n : Type*} [CommSemiring R] [Semiring α] [StarRing α] [Algebra R α]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [TopologicalSpace α]

@[continuity, fun_prop]
theorem continuous_kroneckerOneStarAlgHom :
    Continuous (kroneckerOneStarAlgHom R (α := α) (m := m) n) :=
  (continuous_pi fun _ ↦ continuous_id).matrix_blockDiagonal.congr fun A ↦
    (kronecker_one A).symm.trans (kroneckerOneStarAlgHom_apply A).symm

@[continuity, fun_prop]
theorem continuous_oneKroneckerStarAlgHom :
    Continuous (oneKroneckerStarAlgHom R (α := α) (m := m) n) :=
  ((continuous_pi fun _ ↦ continuous_id).matrix_blockDiagonal.matrix_reindex _ _).congr fun B ↦
    (one_kronecker B).symm.trans (oneKroneckerStarAlgHom_apply B).symm

end Matrix

namespace Matrix

open Filter Topology in
/-- Convergence of a matrix-valued function is entrywise convergence. -/
theorem tendsto_iff_tendsto_apply {α m n R : Type*} [TopologicalSpace R] {l : Filter α}
    {M : α → Matrix m n R} {D : Matrix m n R} :
    Tendsto M l (𝓝 D) ↔ ∀ i j, Tendsto (fun x ↦ M x i j) l (𝓝 (D i j)) :=
  tendsto_pi_nhds.trans <| forall_congr' fun _ ↦ tendsto_pi_nhds

open Filter Topology in
/-- A matrix-valued function converges exactly when its products with every column vector do. -/
theorem tendsto_iff_forall_tendsto_mulVec {α m n R : Type*} [Fintype n] [NonAssocSemiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] {l : Filter α} {M : α → Matrix m n R}
    {D : Matrix m n R} :
    Tendsto M l (𝓝 D) ↔ ∀ v, Tendsto (fun x ↦ M x *ᵥ v) l (𝓝 (D *ᵥ v)) := by
  classical
  refine ⟨fun h v ↦ ((continuous_id.matrix_mulVec continuous_const).tendsto D).comp h,
    fun h ↦ tendsto_iff_tendsto_apply.2 fun i j ↦ ?_⟩
  simpa [mulVec_single_one] using tendsto_pi_nhds.1 (h (Pi.single j 1)) i

open Filter Topology in
/-- Square matrices tending to the identity along a filter eventually have nonzero determinant. -/
theorem eventually_det_ne_zero_of_tendsto_one {α n R : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R] [Nontrivial R]
    {l : Filter α} {M : α → Matrix n n R} (hM : Tendsto M l (𝓝 1)) :
    ∀ᶠ x in l, (M x).det ≠ 0 :=
  (((continuous_id.matrix_det).tendsto 1).comp hM).eventually_ne (by simp)

/-- The matrices with nonnegative diagonal form a closed set. -/
theorem isClosed_setOfPred_nonneg_diag {n R : Type*} [TopologicalSpace R] [Zero R] [Preorder R]
    [OrderClosedTopology R] : IsClosed {M : Matrix n n R | ∀ i, 0 ≤ M i i} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_id.matrix_elem i i)

end Matrix

namespace LinearMap

open Filter Topology in
/-- Pointwise convergence of sesquilinear forms gives convergence of their Gram matrices in any
pair of finite bases. -/
theorem tendsto_toMatrix₂ {R M₁ M₂ N₂ n m α : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂] [Module R N₂]
    [TopologicalSpace N₂] {σ₁ σ₂ : R →+* R} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (b₁ : Module.Basis n R M₁) (b₂ : Module.Basis m R M₂) {l : Filter α}
    {B : α → M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂} {B₀ : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] N₂}
    (hB : ∀ u v, Tendsto (fun a ↦ B a u v) l (𝓝 (B₀ u v))) :
    Tendsto (fun a ↦ toMatrix₂ b₁ b₂ (B a)) l (𝓝 (toMatrix₂ b₁ b₂ B₀)) :=
  Matrix.tendsto_iff_tendsto_apply.2 fun i j ↦ by
    simpa only [toMatrix₂_apply] using hB (b₁ i) (b₂ j)

end LinearMap

/-- The matrices whose entries all lie in a dense set `S` form a dense set. -/
theorem Dense.matrix {m n R : Type*} [TopologicalSpace R] {S : Set R} (hS : Dense S) :
    Dense (S.matrix : Set (Matrix m n R)) := by
  rw [Set.matrix_eq_pi]
  exact (dense_pi Set.univ fun _ _ ↦ dense_pi Set.univ fun _ _ ↦ hS).preimage
    Matrix.ofHomeomorph.symm.isOpenMap
