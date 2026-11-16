/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.LinearAlgebra.TensorProduct.FiniteExtension
import TauCeti.RepresentationTheory.GaloisDescent.Injective
import TauCeti.RepresentationTheory.GaloisDescent.Range
import TauCeti.RepresentationTheory.GaloisDescent.Span
import TauCeti.RepresentationTheory.Quotient

/-!
# Semilinear Galois descent for infinite Galois extensions

Let `L / k` be a Galois extension, possibly of infinite degree, and equip `Gal(L/k)` with its Krull
topology. A semilinear representation `ρ` of `Gal(L/k)` on an `L`-vector space `V` is *discrete*
(or continuous for the discrete topology on `V`) when every vector `v ∈ V` has an open stabilizer
`{g ∈ Gal(L/k) | ρ g v = v}`.

This file extends the three steps of semilinear Galois descent from finite Galois groups
(`TauCeti.RepresentationTheory.GaloisDescent.Injective`,
`TauCeti.RepresentationTheory.GaloisDescent.Range`, and
`TauCeti.RepresentationTheory.GaloisDescent.Span`) to arbitrary Galois extensions `L / k`.
Injectivity and recognition of invariants require no topological hypothesis on `ρ`, because any
tensor in `L ⊗[k] W` involves only finitely many scalars in `L` and therefore lives over a finite
Galois subextension. Spanning (Speiser's theorem) holds if and only if all stabilizers are open.
No characteristic restriction and no finite-dimensionality of `V` over `L` is assumed.

## Main results

* `TauCeti.GaloisDescent.liftBaseChange_injective_of_invariant_of_isGalois`: an injective
  `k`-linear map into `V` whose `L`-multiples transform semilinearly remains injective after
  extending scalars to `L`.
* `TauCeti.GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective_of_isGalois`: an
  invariant `k`-linear map whose scalar extension to `L` is surjective has range equal to
  `ρ.invariants`.
* `TauCeti.GaloisDescent.span_invariants_eq_top_of_isOpen`,
  `TauCeti.GaloisDescent.isOpen_of_span_invariants_eq_top`, and
  `TauCeti.GaloisDescent.span_invariants_eq_top_iff_forall_isOpen`: the invariant vectors span `V`
  over `L` if and only if every vector in `V` has an open stabilizer in `Gal(L/k)`.
* `TauCeti.GaloisDescent.liftBaseChange_invariants_bijective_of_isOpen`: when all stabilizers are
  open, the scalar extension `L ⊗[k] ρ.invariants →ₗ[L] V` is bijective.

## References

* A. Speiser, *Zahlentheoretische Untersuchungen*, Mathematische Annalen 80 (1919), 20–31.
* N. Bourbaki, *Algebra II*, Chapters 4–7, Springer, Chapter V, §10.4, Proposition 8.
* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open IntermediateField
open scoped TensorProduct Topology

namespace TauCeti.GaloisDescent

variable {k L V : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]

section Map

variable {W : Type*} [AddCommGroup W] [Module k W]

/-- For `f : W →ₗ[k] V` whose `L`-multiples transform semilinearly, `Submodule.span E (Set.range f)`
is preserved by `Gal(L/k)` and fixed pointwise by `E.fixingSubgroup`. -/
private theorem span_range_mem_and_fix {ρ : Representation k Gal(L/k) V}
    {f : W →ₗ[k] V} (hsemi : ∀ (g : Gal(L/k)) (a : L) (w : W), ρ g (a • f w) = g a • f w)
    (E : IntermediateField k L) [Normal k E] :
    (∀ (g : Gal(L/k)) ⦃u : V⦄,
      u ∈ Submodule.span E (Set.range f) → ρ g u ∈ Submodule.span E (Set.range f)) ∧
      (∀ {g : Gal(L/k)}, g ∈ E.fixingSubgroup →
        ∀ {u : V}, u ∈ Submodule.span E (Set.range f) → ρ g u = u) := by
  have : IsScalarTower k E V := E.toSubalgebra.isScalarTower_mid
  have hmain {u : V} (hu : u ∈ Submodule.span E (Set.range f)) (g : Gal(L/k)) :
      ρ g u ∈ Submodule.span E (Set.range f) ∧
        (g ∈ E.fixingSubgroup → ρ g u = u) ∧
        ∀ b : E, ρ g (b • u) = AlgEquiv.restrictNormalHom E g b • ρ g u := by
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨w, rfl⟩ := hx
      have hfw : ρ g (f w) = f w := by simpa using hsemi g 1 w
      refine ⟨hfw.symm ▸ Submodule.subset_span ⟨w, rfl⟩, fun _ ↦ hfw, fun b ↦ ?_⟩
      rw [hfw, Subalgebra.smul_def, hsemi, ← AlgEquiv.restrictNormalHom_apply E g b,
        Subalgebra.smul_def]
    | zero => simp
    | add _ _ _ _ hx hy =>
      refine ⟨by rw [map_add]; exact add_mem hx.1 hy.1,
        fun hg ↦ by rw [map_add, hx.2.1 hg, hy.2.1 hg], fun b ↦ ?_⟩
      rw [smul_add, map_add, hx.2.2 b, hy.2.2 b, map_add, smul_add]
    | smul a x _ hx =>
      rw [hx.2.2 a]
      refine ⟨Submodule.smul_mem _ _ hx.1, fun hg ↦ ?_, fun b ↦ ?_⟩
      · have ha : AlgEquiv.restrictNormalHom E g a = a := by
          rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker] at hg
          simp [hg]
        rw [ha, hx.2.1 hg]
      · rw [← mul_smul, hx.2.2 (b * a), map_mul, mul_smul]
  exact ⟨fun g _ hu ↦ (hmain hu g).1, fun hg _ hu ↦ (hmain hu _).2.1 hg⟩

/-- **Injectivity in semilinear Galois descent for arbitrary Galois extensions.** Let `L / k` be a
Galois extension, possibly infinite, and `ρ` a `k`-linear representation of `Gal(L/k)` on an
`L`-vector space `V`. An injective `k`-linear map `f : W →ₗ[k] V` whose `L`-multiples transform
semilinearly remains injective after extending scalars to `L`. No open-stabilizer hypothesis on `ρ`
and no dimension bound on `V` or `W` is required. -/
theorem liftBaseChange_injective_of_invariant_of_isGalois [IsGalois k L]
    {ρ : Representation k Gal(L/k) V} {f : W →ₗ[k] V} (hf : Function.Injective f)
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (w : W), ρ g (a • f w) = g a • f w) :
    Function.Injective (f.liftBaseChange L) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨E, hfin, hnorm, hzE⟩ :=
    Set.exists_normal_intermediateField_subset_range_rTensor {z} (Set.finite_singleton z)
  obtain ⟨z₀, rfl⟩ := hzE (Set.mem_singleton z)
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E L
  have : IsGalois k E := ⟨⟩
  have : IsScalarTower k E V := E.toSubalgebra.isScalarTower_mid
  let U : Submodule E V := Submodule.span E (Set.range f)
  obtain ⟨hU_mem, hU_fix⟩ := span_range_mem_and_fix hsemi E
  let U' : Subrepresentation ρ := ⟨U.restrictScalars k, hU_mem⟩
  have : Representation.IsTrivial
      (U'.toRepresentation.comp (AlgEquiv.restrictNormalHom E).ker.subtype) :=
    ⟨fun ⟨g, hg⟩ ↦ LinearMap.ext fun u ↦ Subtype.ext <|
      hU_fix (E.restrictNormalHom_ker ▸ hg) u.2⟩
  let ρE : Representation k Gal(E/k) (U.restrictScalars k) :=
    U'.toRepresentation.ofSurjective (AlgEquiv.restrictNormalHom E)
      (AlgEquiv.restrictNormalHom_surjective L)
  let fE : W →ₗ[k] U.restrictScalars k :=
    f.codRestrict (U.restrictScalars k) fun w ↦ Submodule.subset_span ⟨w, rfl⟩
  have hfE : Function.Injective fE := fun _ _ h ↦ hf (congrArg Subtype.val h)
  have hsemiE (σ : Gal(E/k)) (a : E) (w : W) : ρE σ (a • fE w) = (σ • a) • fE w := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    rw [Representation.ofSurjective_apply, Subrepresentation.toRepresentation_apply_coe]
    exact (hsemi g a w).trans (by rw [← AlgEquiv.restrictNormalHom_apply E g a]; rfl)
  have hinj := liftBaseChange_injective_of_invariant (ρ := ρE) hfE hsemiE
  have hcomp :
      (U.restrictScalars k).subtype ∘ₗ (fE.liftBaseChange E).restrictScalars k =
        (f.liftBaseChange L).restrictScalars k ∘ₗ LinearMap.rTensor W E.val.toLinearMap :=
    TensorProduct.ext' fun _ _ ↦ rfl
  have hz₀ : z₀ = 0 := hinj <| by
    rw [map_zero]
    exact Subtype.ext (by simpa [hz] using LinearMap.congr_fun hcomp z₀)
  rw [hz₀, map_zero]

/-- **Recognizing invariant vectors for arbitrary Galois extensions.** Let `L / k` be a Galois
extension, possibly infinite, and `ρ` a semilinear representation of `Gal(L/k)` on `V`. An
invariant `k`-linear map `f : W →ₗ[k] V` whose scalar extension to `L` is surjective has range
equal to `ρ.invariants`. -/
theorem range_eq_invariants_of_liftBaseChange_surjective_of_isGalois [IsGalois k L]
    {ρ : Representation k Gal(L/k) V} {f : W →ₗ[k] V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v)
    (hinv : ∀ (g : Gal(L/k)) (w : W), ρ g (f w) = f w)
    (hf : Function.Surjective (f.liftBaseChange L)) :
    LinearMap.range f = ρ.invariants := by
  refine le_antisymm (by rintro _ ⟨w, rfl⟩; exact (ρ.mem_invariants _).mpr (hinv · w)) fun v hv ↦ ?_
  obtain ⟨z, rfl⟩ := hf v
  obtain ⟨E, hfin, hnorm, hzE⟩ :=
    Set.exists_normal_intermediateField_subset_range_rTensor {z} (Set.finite_singleton z)
  obtain ⟨z₀, rfl⟩ := hzE (Set.mem_singleton z)
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E L
  have : IsGalois k E := ⟨⟩
  have : IsScalarTower k E V := E.toSubalgebra.isScalarTower_mid
  let U : Submodule E V := Submodule.span E (Set.range f)
  obtain ⟨hU_mem, hU_fix⟩ :=
    span_range_mem_and_fix (fun g a w ↦ by rw [hsemi, hinv]) E
  let U' : Subrepresentation ρ := ⟨U.restrictScalars k, hU_mem⟩
  have : Representation.IsTrivial
      (U'.toRepresentation.comp (AlgEquiv.restrictNormalHom E).ker.subtype) :=
    ⟨fun ⟨g, hg⟩ ↦ LinearMap.ext fun u ↦ Subtype.ext <|
      hU_fix (E.restrictNormalHom_ker ▸ hg) u.2⟩
  let ρE : Representation k Gal(E/k) (U.restrictScalars k) :=
    U'.toRepresentation.ofSurjective (AlgEquiv.restrictNormalHom E)
      (AlgEquiv.restrictNormalHom_surjective L)
  let fE : W →ₗ[k] U.restrictScalars k :=
    f.codRestrict (U.restrictScalars k) fun w ↦ Submodule.subset_span ⟨w, rfl⟩
  have hsemiE (σ : Gal(E/k)) (a : E) (u : U.restrictScalars k) :
      ρE σ (a • u) = (σ • a) • ρE σ u := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    rw [Representation.ofSurjective_apply, Subrepresentation.toRepresentation_apply_coe]
    exact (hsemi g a u).trans (by
      rw [← AlgEquiv.restrictNormalHom_apply E g a]
      exact congrArg ((AlgEquiv.restrictNormalHom E g a : L) • ·) rfl)
  have hinvE (σ : Gal(E/k)) (w : W) : ρE σ (fE w) = fE w := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    rw [Representation.ofSurjective_apply, Subrepresentation.toRepresentation_apply_coe]
    exact hinv g w
  have hsurjE : Function.Surjective (fE.liftBaseChange E) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, eq_top_iff]
    rintro ⟨u, hu⟩ -
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, rfl⟩
    | zero => exact zero_mem _
    | add _ _ _ _ ihx ihy => exact add_mem ihx ihy
    | smul a _ _ ihx => exact Submodule.smul_mem _ a ihx
  let u₀ : U.restrictScalars k := fE.liftBaseChange E z₀
  have hcomp :
      (U.restrictScalars k).subtype ∘ₗ (fE.liftBaseChange E).restrictScalars k =
        (f.liftBaseChange L).restrictScalars k ∘ₗ LinearMap.rTensor W E.val.toLinearMap :=
    TensorProduct.ext' fun _ _ ↦ rfl
  have hu₀_val : (u₀ : V) = f.liftBaseChange L (LinearMap.rTensor W E.val.toLinearMap z₀) :=
    LinearMap.congr_fun hcomp z₀
  have hu₀_inv : u₀ ∈ ρE.invariants := (ρE.mem_invariants u₀).mpr fun σ ↦ by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    rw [Representation.ofSurjective_apply, Subrepresentation.toRepresentation_apply_coe, hu₀_val]
    exact (ρ.mem_invariants _).mp hv g
  rw [← range_eq_invariants_of_liftBaseChange_surjective hsemiE hinvE hsurjE] at hu₀_inv
  obtain ⟨w, hw⟩ := hu₀_inv
  exact ⟨w, (congrArg Subtype.val hw).trans hu₀_val⟩

end Map

/-- **Speiser's theorem (discrete semilinear Galois descent).** Let `L / k` be a Galois extension,
possibly infinite, and let `ρ` be a semilinear representation of `Gal(L/k)` on an `L`-vector space
`V`. If every vector `v ∈ V` has an open stabilizer in `Gal(L/k)` for the Krull topology, then `V`
is spanned over `L` by `ρ.invariants`. -/
theorem span_invariants_eq_top_of_isOpen [IsGalois k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v)
    (hopen : ∀ v : V, IsOpen {g : Gal(L/k) | ρ g v = v}) :
    Submodule.span L (ρ.invariants : Set V) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  have hnhds : {g : Gal(L/k) | ρ g v = v} ∈ 𝓝 (1 : Gal(L/k)) :=
    (hopen v).mem_nhds (by simp)
  obtain ⟨E, hfin, hnorm, hfix_v⟩ := (krullTopology_mem_nhds_one_iff_of_normal k L _).mp hnhds
  have : IsScalarTower k E V := E.toSubalgebra.isScalarTower_mid
  let S : Set V := Set.range fun g : Gal(L/k) ↦ ρ g v
  let U : Submodule E V := Submodule.span E S
  have hU_mem (σ : Gal(L/k)) ⦃u : V⦄ (hu : u ∈ U) : ρ σ u ∈ U := by
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [← mul_apply_eq_comp, ← map_mul]
      exact Submodule.subset_span ⟨σ * g, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a _ _ hx =>
      rw [Subalgebra.smul_def, hsemi, ← AlgEquiv.restrictNormalHom_apply E σ a,
        ← Subalgebra.smul_def]
      exact U.smul_mem _ hx
  have hU_fix {h : Gal(L/k)} (hh : h ∈ E.fixingSubgroup) {u : V} (hu : u ∈ U) :
      ρ h u = u := by
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨g, rfl⟩ := hx
      have hconj : g⁻¹ * h * g ∈ E.fixingSubgroup := by
        rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker] at hh ⊢
        simp [hh]
      have hv' := congrArg (ρ g) (hfix_v hconj)
      simpa [← mul_apply_eq_comp, ← map_mul, mul_assoc] using hv'
    | zero => exact map_zero _
    | add _ _ _ _ hx hy => rw [map_add, hx, hy]
    | smul a _ _ hx =>
      rw [Subalgebra.smul_def, hsemi, (mem_fixingSubgroup_iff E h).mp hh a a.2, hx,
        ← Subalgebra.smul_def]
  let U' : Subrepresentation ρ := ⟨U.restrictScalars k, hU_mem⟩
  have : Representation.IsTrivial
      (U'.toRepresentation.comp (AlgEquiv.restrictNormalHom E).ker.subtype) :=
    ⟨fun ⟨g, hg⟩ ↦ LinearMap.ext fun u ↦ Subtype.ext <|
      hU_fix (E.restrictNormalHom_ker ▸ hg) u.2⟩
  let ρE : Representation k Gal(E/k) (U.restrictScalars k) :=
    U'.toRepresentation.ofSurjective (AlgEquiv.restrictNormalHom E)
      (AlgEquiv.restrictNormalHom_surjective L)
  have hsemiE (σ : Gal(E/k)) (a : E) (u : U.restrictScalars k) :
      ρE σ (a • u) = (σ • a) • ρE σ u := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    rw [Representation.ofSurjective_apply, Subrepresentation.toRepresentation_apply_coe]
    exact (hsemi g a u).trans (by
      rw [← AlgEquiv.restrictNormalHom_apply E g a]
      exact congrArg ((AlgEquiv.restrictNormalHom E g a : L) • ·) rfl)
  have hspanE := span_invariants_eq_top (ρ := ρE) hsemiE
  have hvU : (⟨v, Submodule.subset_span ⟨1, by simp⟩⟩ : U.restrictScalars k) ∈
      Submodule.span E (ρE.invariants : Set (U.restrictScalars k)) :=
    hspanE ▸ Submodule.mem_top
  suffices ∀ u ∈ Submodule.span E (ρE.invariants : Set (U.restrictScalars k)),
      (u : V) ∈ Submodule.span L (ρ.invariants : Set V) from this _ hvU
  intro u hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    refine Submodule.subset_span ((ρ.mem_invariants (w : V)).mpr fun g ↦ ?_)
    have hg := (ρE.mem_invariants w).mp hw (AlgEquiv.restrictNormalHom E g)
    rwa [Representation.ofSurjective_apply, Subrepresentation.toRepresentation_apply_coe] at hg
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a _ _ hx => exact Submodule.smul_mem _ (a : L) hx

omit [IsScalarTower k L V] in
/-- **Vectors spanned by invariants have open stabilizers.** Over an algebraic extension `L / k`,
if `V` is spanned over `L` by the invariants of a semilinear representation `ρ` of `Gal(L/k)` on
`V`, then every vector in `V` has an open stabilizer in `Gal(L/k)` for the Krull topology. -/
theorem isOpen_of_span_invariants_eq_top [Algebra.IsIntegral k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v)
    (hspan : Submodule.span L (ρ.invariants : Set V) = ⊤) (v : V) :
    IsOpen {g : Gal(L/k) | ρ g v = v} := by
  let stabSubgroup (w : V) : Subgroup Gal(L/k) :=
    { carrier := {g | ρ g w = w}
      one_mem' := by simp
      mul_mem' {g h} hg hh := by
        rw [Set.mem_ofPred_eq, map_mul, mul_apply_eq_comp, hh, hg]
      inv_mem' {g} hg := by
        rw [Set.mem_ofPred_eq]
        have := congrArg (ρ g⁻¹) hg
        simpa [← mul_apply_eq_comp, ← map_mul] using this.symm }
  have hv : v ∈ Submodule.span L (ρ.invariants : Set V) := hspan ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    exact Subgroup.isOpen_mono (H₁ := ⊤) (H₂ := stabSubgroup x)
      (fun g _ ↦ (ρ.mem_invariants x).mp hx g) isOpen_univ
  | zero =>
    exact Subgroup.isOpen_mono (H₁ := ⊤) (H₂ := stabSubgroup 0)
      (fun g _ ↦ map_zero (ρ g)) isOpen_univ
  | add x y _ _ hx hy =>
    exact Subgroup.isOpen_mono (H₁ := stabSubgroup x ⊓ stabSubgroup y) (H₂ := stabSubgroup (x + y))
      (fun g ⟨hgx, hgy⟩ ↦ (map_add (ρ g) x y).trans (congrArg₂ (· + ·) hgx hgy))
      (hx.inter hy)
  | smul a x _ hx =>
    exact Subgroup.isOpen_mono
      (H₁ := MulAction.stabilizer Gal(L/k) a ⊓ stabSubgroup x) (H₂ := stabSubgroup (a • x))
      (fun g ⟨hga, hgx⟩ ↦
        (hsemi g a x).trans (by rw [← AlgEquiv.smul_def, MulAction.mem_stabilizer_iff.mp hga, hgx]))
      ((stabilizer_isOpen_of_isIntegral a).inter hx)

/-- **Characterization of discrete semilinear Galois representations.** For a Galois extension
`L / k` and a semilinear representation `ρ` of `Gal(L/k)` on an `L`-vector space `V`, the invariant
vectors span `V` over `L` if and only if every vector in `V` has an open stabilizer in `Gal(L/k)`.
-/
theorem span_invariants_eq_top_iff_forall_isOpen [IsGalois k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v) :
    Submodule.span L (ρ.invariants : Set V) = ⊤ ↔
      ∀ v : V, IsOpen {g : Gal(L/k) | ρ g v = v} :=
  ⟨isOpen_of_span_invariants_eq_top hsemi, span_invariants_eq_top_of_isOpen hsemi⟩

/-- **Effectiveness of discrete semilinear Galois descent.** For a Galois extension `L / k` and a
semilinear representation `ρ` of `Gal(L/k)` on `V` whose vectors all have open stabilizers, the
canonical scalar-extension map `L ⊗[k] ρ.invariants →ₗ[L] V` is bijective. -/
theorem liftBaseChange_invariants_bijective_of_isOpen [IsGalois k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v)
    (hopen : ∀ v : V, IsOpen {g : Gal(L/k) | ρ g v = v}) :
    Function.Bijective (ρ.invariants.subtype.liftBaseChange L) := by
  refine ⟨liftBaseChange_injective_of_invariant_of_isGalois (ρ := ρ) Subtype.val_injective
    fun g a w ↦ by rw [Submodule.coe_subtype, hsemi, (ρ.mem_invariants w.1).mp w.2 g], ?_⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, Submodule.range_subtype,
    span_invariants_eq_top_of_isOpen hsemi hopen]

end TauCeti.GaloisDescent
