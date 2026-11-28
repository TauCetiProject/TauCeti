/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.Dual.Basis

/-!
# Lattices in the linear dual

The integral dual of an `R`-submodule of a `K`-module consists of the `K`-linear
functionals taking values in `R` on that submodule. This construction requires no
bilinear form on the ambient module. For the span of a finite basis it is the span
of the dual basis; in particular the dual of a free full lattice is a full lattice.

Precomposition carries integral duals contravariantly along lattice-preserving
linear maps, and the integral dual of a homothetic image `c • N` is `c⁻¹` times the
integral dual of `N`. This is the linear-algebra input to contragredient actions on
admissible integral lattices.

Evaluation identifies a free full lattice with its double integral dual: the double dual
of `N` is the image of `N` in the double dual space.

Evaluation restricts to an `R`-valued pairing between the integral dual and the
submodule. When `R` embeds in `K`, this pairing is perfect for a free full lattice:
its integral dual is its `R`-linear dual.
-/

public section

open scoped Pointwise

namespace Submodule

variable {R K V W : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V]
  [AddCommGroup W] [Module K W] [Module R W]

variable (K) in
/-- The linear functionals taking values in the image of `R` on `N`.
No bilinear form or full-lattice hypothesis is required. -/
def dualLattice (N : Submodule R V) : Submodule R (Module.Dual K V) :=
  ⨅ x : N, (1 : Submodule R K).comap
    ((LinearMap.applyₗ (R := K) (M₂ := K) (x : V)).restrictScalars R)

/-- Membership in the integral dual is integrality of every evaluation on the original
submodule. -/
@[simp]
theorem mem_dualLattice (N : Submodule R V) (φ : Module.Dual K V) :
    φ ∈ N.dualLattice K ↔ ∀ x ∈ N, φ x ∈ (1 : Submodule R K) := by
  simp [dualLattice]

/-- A functional is integral on a span exactly when it is integral on the spanning set. -/
theorem mem_dualLattice_span_iff [IsScalarTower R K V] (s : Set V) (φ : Module.Dual K V) :
    φ ∈ (span R s).dualLattice K ↔ ∀ x ∈ s, φ x ∈ (1 : Submodule R K) := by
  refine ⟨fun hφ x hx ↦ (mem_dualLattice _ φ).mp hφ x (subset_span hx), fun h ↦ ?_⟩
  have : span R s ≤ (1 : Submodule R K).comap (φ.restrictScalars R) := span_le.mpr h
  exact (mem_dualLattice _ φ).mpr fun x hx ↦ this hx

variable (K) in
/-- Taking the integral dual reverses inclusions. -/
theorem dualLattice_antitone : Antitone (dualLattice (R := R) (V := V) K) := by
  intro M N h φ hφ
  exact (mem_dualLattice M φ).mpr fun x hx => (mem_dualLattice N φ).mp hφ x (h hx)

/-- Precomposition with a lattice-preserving map preserves the corresponding integral duals. -/
theorem dualMap_mem_dualLattice (M : Submodule R V) (N : Submodule R W)
    (f : V →ₗ[K] W) (hf : ∀ x ∈ M, f x ∈ N)
    {φ : Module.Dual K W} (hφ : φ ∈ N.dualLattice K) :
    f.dualMap φ ∈ M.dualLattice K := by
  exact (mem_dualLattice M _).mpr fun x hx => (mem_dualLattice N φ).mp hφ _ (hf x hx)

/-- The integral dual of a homothetic submodule `c • N` is `c⁻¹` times the integral dual
of `N`. -/
@[simp]
theorem dualLattice_smul [IsScalarTower R K V] (c : Kˣ) (N : Submodule R V) :
    (c • N).dualLattice K = c⁻¹ • N.dualLattice K := by
  ext φ
  simp only [Units.smul_def, mem_dualLattice, mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    refine ⟨(c : K) • φ, fun x hx ↦ ?_, ?_⟩
    · simpa using h ((c : K) • x) ⟨x, hx, rfl⟩
    · simp [smul_smul]
  · rintro ⟨ψ, hψ, rfl⟩ _ ⟨x, hx, rfl⟩
    simpa [smul_smul] using hψ x hx

end Submodule

namespace Module.Basis

variable {R K V ι : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [Finite ι] [DecidableEq ι]

/-- The integral dual of a basis lattice is the lattice spanned by the dual basis. -/
@[simp]
theorem dualLattice_span (b : Basis ι K V) :
    (Submodule.span R (Set.range b)).dualLattice K =
      Submodule.span R (Set.range b.dualBasis) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro φ hφ
    rw [← b.dualBasis.sum_repr φ]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [dualBasis_repr]
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp
      ((Submodule.mem_dualLattice _ _).mp hφ _ (Submodule.subset_span ⟨i, rfl⟩))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine (Submodule.mem_dualLattice _ _).mpr ?_
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [dualBasis_apply_self]
      split
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => simpa using (1 : Submodule R K).add_mem hx hy
    | smul r x _ hx => simpa using (1 : Submodule R K).smul_mem r hx

omit [DecidableEq ι] in
/-- The double integral dual of a basis lattice is its image under evaluation in the double
dual. -/
theorem dualLattice_dualLattice_span (b : Basis ι K V) :
    ((Submodule.span R (Set.range b)).dualLattice K).dualLattice K =
      (Submodule.span R (Set.range b)).map ((Module.Dual.eval K V).restrictScalars R) := by
  classical
  rw [b.dualLattice_span, b.dualBasis.dualLattice_span, Submodule.map_span, ← Set.range_comp]
  congr 2
  ext i
  simp

end Module.Basis

namespace Submodule

section IsFractionRing

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/-- The integral dual of a free full lattice is again a full lattice. -/
instance isFullLattice_dualLattice (N : Submodule R V) [N.IsFullLattice K] [Module.Free R N] :
    (N.dualLattice K).IsFullLattice K := by
  classical
  have := IsLattice.finite K N
  let b := Module.Free.chooseBasis R N
  rw [← b.span_range_extendOfIsFullLattice (K := K), (b.extendOfIsFullLattice K).dualLattice_span]
  exact (b.extendOfIsFullLattice K).dualBasis.isFullLattice_span_range

omit [IsFractionRing R K] in
/-- **Biduality for lattices.** Evaluation carries a free full lattice onto its double integral
dual. -/
theorem dualLattice_dualLattice (N : Submodule R V) [N.IsFullLattice K] [Module.Free R N] :
    (N.dualLattice K).dualLattice K = N.map ((Module.Dual.eval K V).restrictScalars R) := by
  have := IsLattice.finite K N
  let b := Module.Free.chooseBasis R N
  rw [← b.span_range_extendOfIsFullLattice (K := K)]
  exact (b.extendOfIsFullLattice K).dualLattice_dualLattice_span

end IsFractionRing

section Pairing

variable {R K V : Type*} [CommRing R] [CommRing K] [Algebra R K] [FaithfulSMul R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable (K) in
/-- The `R`-valued evaluation pairing between the integral dual of `N` and `N`. -/
noncomputable def dualLatticePairing (N : Submodule R V) :
    N.dualLattice K →ₗ[R] N →ₗ[R] R :=
  LinearMap.restrictScalarsRange₂ (N.dualLattice K).subtype N.subtype (Algebra.linearMap R K)
    (FaithfulSMul.algebraMap_injective R K) LinearMap.id fun φ x ↦
      Submodule.mem_one.mp ((mem_dualLattice N _).mp φ.property x x.property)

/-- The integral pairing is evaluation, read back in `K`. -/
@[simp]
theorem algebraMap_dualLatticePairing (N : Submodule R V) (φ : N.dualLattice K) (x : N) :
    algebraMap R K (N.dualLatticePairing K φ x) = (φ : Module.Dual K V) x :=
  LinearMap.restrictScalarsRange₂_apply (N.dualLattice K).subtype N.subtype (Algebra.linearMap R K)
    (FaithfulSMul.algebraMap_injective R K) LinearMap.id _ φ x

/-- **The integral dual of a free full lattice is its `R`-linear dual.** Evaluation pairs the
integral dual of `N` perfectly with `N`: every `R`-linear functional on `N` extends uniquely to a
`K`-linear functional on the ambient space. -/
instance isPerfPair_dualLatticePairing (N : Submodule R V) [N.IsFullLattice K] [Module.Free R N] :
    (N.dualLatticePairing K).IsPerfPair := by
  have := IsLattice.finite K N
  refine .of_bijective _ ⟨fun φ ψ h ↦ ?_, fun g ↦ ?_⟩
  · refine Subtype.ext <| LinearMap.ext_on (IsFullLattice.span_eq_top (A := K) (M := N))
      fun x hx ↦ ?_
    simpa using congr(algebraMap R K ($h ⟨x, hx⟩))
  · -- Extend `g` along the `K`-basis of `V` given by an `R`-basis of `N`.
    let b := Module.Free.chooseBasis R N
    let φ : Module.Dual K V := (b.extendOfIsFullLattice K).constr K fun i ↦ algebraMap R K (g (b i))
    have hφ (x : N) : φ x = algebraMap R K (g x) := by
      have : (φ.restrictScalars R).comp N.subtype = (Algebra.linearMap R K).comp g :=
        b.ext fun i ↦ by
          rw [LinearMap.comp_apply, Submodule.subtype_apply,
            ← Module.Basis.extendOfIsFullLattice_apply K b, LinearMap.restrictScalars_apply,
            Module.Basis.constr_basis, LinearMap.comp_apply, Algebra.linearMap_apply]
      exact congr($this x)
    refine ⟨⟨φ, (mem_dualLattice N φ).mpr fun x hx ↦
      Submodule.mem_one.mpr ⟨g ⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩⟩, LinearMap.ext fun x ↦ ?_⟩
    apply FaithfulSMul.algebraMap_injective R K
    simp [hφ]

end Pairing

end Submodule
