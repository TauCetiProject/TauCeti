/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RepresentationTheory.Stabilizer
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.LinearAlgebra.TensorProduct.FiniteExtension
import TauCeti.RepresentationTheory.GaloisDescent.Injective
import TauCeti.RepresentationTheory.GaloisDescent.Range
import TauCeti.RepresentationTheory.GaloisDescent.Span
import TauCeti.RepresentationTheory.Quotient
import TauCeti.RepresentationTheory.Subrepresentation

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

## Main definitions

* `TauCeti.GaloisDescent.openStabilizerSubmodule`: the `L`-submodule of vectors in `V` with open
  stabilizer in `Gal(L/k)`.

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

* A. Speiser, *Zahlentheoretische Sätze aus der Gruppentheorie*, Mathematische Zeitschrift 5
  (1919), 1–6.
* N. Bourbaki, *Algebra II*, Chapters 4–7, Springer, Chapter V, §10.4, Proposition 8.
* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open IntermediateField
open scoped TensorProduct Topology

namespace TauCeti.GaloisDescent

variable {k L V : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]

section NormalSubextension

variable {E : IntermediateField k L} [Normal k E]

omit [IsScalarTower k L V] in
/-- If a set `S` is mapped into `Submodule.span E S` by `Gal(L/k)`, fixed pointwise by
`E.fixingSubgroup`, and `E`-multiples of its elements transform semilinearly, then
`Submodule.span E S` has the same three properties. -/
private theorem span_mem_and_fix {ρ : Representation k Gal(L/k) V} {S : Set V}
    (hS_mem : ∀ (g : Gal(L/k)), ∀ x ∈ S, ρ g x ∈ Submodule.span E S)
    (hS_fix : ∀ ⦃g : Gal(L/k)⦄, g ∈ E.fixingSubgroup → ∀ x ∈ S, ρ g x = x)
    (hS_smul : ∀ (g : Gal(L/k)) (a : E), ∀ x ∈ S,
      ρ g (a • x) = AlgEquiv.restrictNormalHom E g a • ρ g x) :
    (∀ (g : Gal(L/k)) ⦃u : V⦄, u ∈ Submodule.span E S → ρ g u ∈ Submodule.span E S) ∧
      (∀ ⦃g : Gal(L/k)⦄, g ∈ E.fixingSubgroup →
        ∀ ⦃u : V⦄, u ∈ Submodule.span E S → ρ g u = u) ∧
      (∀ (g : Gal(L/k)) (a : E) ⦃u : V⦄, u ∈ Submodule.span E S →
        ρ g (a • u) = AlgEquiv.restrictNormalHom E g a • ρ g u) := by
  have hmain {u : V} (hu : u ∈ Submodule.span E S) (g : Gal(L/k)) :
      ρ g u ∈ Submodule.span E S ∧
        (g ∈ E.fixingSubgroup → ρ g u = u) ∧
        ∀ b : E, ρ g (b • u) = AlgEquiv.restrictNormalHom E g b • ρ g u := by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      exact ⟨hS_mem g x hx, fun hg ↦ hS_fix hg x hx, fun b ↦ hS_smul g b x hx⟩
    | zero => simp
    | add _ _ _ _ hx hy =>
      refine ⟨by rw [map_add]; exact add_mem hx.1 hy.1,
        fun hg ↦ by rw [map_add, hx.2.1 hg, hy.2.1 hg], fun b ↦ ?_⟩
      rw [smul_add, map_add, hx.2.2 b, hy.2.2 b, map_add, smul_add]
    | smul a _ _ hx =>
      rw [hx.2.2 a]
      refine ⟨Submodule.smul_mem _ _ hx.1, fun hg ↦ ?_, fun b ↦ ?_⟩
      · have ha : AlgEquiv.restrictNormalHom E g a = a := by
          rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker] at hg
          simp [hg]
        rw [ha, hx.2.1 hg]
      · rw [← mul_smul, hx.2.2 (b * a), map_mul, mul_smul]
  exact ⟨fun g _ hu ↦ (hmain hu g).1, fun _ hg _ hu ↦ (hmain hu _).2.1 hg,
    fun g a _ hu ↦ (hmain hu g).2.2 a⟩

variable [IsScalarTower k E V]

omit [IsScalarTower k L V] in
/-- The `Gal(E/k)`-representation on `U.restrictScalars k` induced by a `Gal(L/k)`-stable
`E`-submodule `U` of `V` fixed pointwise by `E.fixingSubgroup`. -/
private noncomputable def descentRep [IsGalois k L] {ρ : Representation k Gal(L/k) V}
    {U : Submodule E V}
    (hU_mem : ∀ (g : Gal(L/k)) ⦃u : V⦄, u ∈ U → ρ g u ∈ U)
    (hU_fix : ∀ ⦃g : Gal(L/k)⦄, g ∈ E.fixingSubgroup → ∀ ⦃u : V⦄, u ∈ U → ρ g u = u) :
    Representation k Gal(E/k) (U.restrictScalars k) :=
  let U' : Subrepresentation ρ :=
    ⟨U.restrictScalars k, fun g _ hu ↦
      (U.restrictScalars_mem k _).mpr (hU_mem g ((U.restrictScalars_mem k _).mp hu))⟩
  haveI : Representation.IsTrivial
      (U'.toRepresentation.comp (AlgEquiv.restrictNormalHom E).ker.subtype) :=
    ⟨fun ⟨_, hg⟩ ↦ LinearMap.ext fun u ↦ Subtype.ext <|
      hU_fix (E.restrictNormalHom_ker ▸ hg) ((U.restrictScalars_mem k _).mp u.property)⟩
  U'.toRepresentation.ofSurjective (AlgEquiv.restrictNormalHom E)
    (AlgEquiv.restrictNormalHom_surjective L)

omit [IsScalarTower k L V] in
private theorem descentRep_restrictNormalHom_coe [IsGalois k L]
    {ρ : Representation k Gal(L/k) V} {U : Submodule E V}
    (hU_mem : ∀ (g : Gal(L/k)) ⦃u : V⦄, u ∈ U → ρ g u ∈ U)
    (hU_fix : ∀ ⦃g : Gal(L/k)⦄, g ∈ E.fixingSubgroup → ∀ ⦃u : V⦄, u ∈ U → ρ g u = u)
    (g : Gal(L/k)) (u : U.restrictScalars k) :
    (descentRep hU_mem hU_fix (AlgEquiv.restrictNormalHom E g) u : V) = ρ g u := by
  rw [descentRep, Representation.ofSurjective_apply, Subrepresentation.coe_toRepresentation_apply]

omit [IsScalarTower k L V] in
private theorem descentRep_smul [IsGalois k L]
    {ρ : Representation k Gal(L/k) V} {U : Submodule E V}
    (hU_mem : ∀ (g : Gal(L/k)) ⦃u : V⦄, u ∈ U → ρ g u ∈ U)
    (hU_fix : ∀ ⦃g : Gal(L/k)⦄, g ∈ E.fixingSubgroup → ∀ ⦃u : V⦄, u ∈ U → ρ g u = u)
    (hU_smul : ∀ (g : Gal(L/k)) (a : E) ⦃u : V⦄, u ∈ U →
      ρ g (a • u) = AlgEquiv.restrictNormalHom E g a • ρ g u)
    (σ : Gal(E/k)) (a : E) (u : U.restrictScalars k) :
    descentRep hU_mem hU_fix σ (a • u) = (σ • a) • descentRep hU_mem hU_fix σ u := by
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  apply Subtype.ext
  exact (descentRep_restrictNormalHom_coe hU_mem hU_fix g (a • u)).trans
    ((hU_smul g a u.property).trans (congrArg (AlgEquiv.restrictNormalHom E g a • ·)
      (descentRep_restrictNormalHom_coe hU_mem hU_fix g u).symm))

end NormalSubextension

section Map

variable {W : Type*} [AddCommGroup W] [Module k W]

local instance (E : IntermediateField k L) : IsScalarTower k E V :=
  E.toSubalgebra.isScalarTower_mid

omit [IsScalarTower k L V] in
private abbrev rangeSpan (f : W →ₗ[k] V) (E : IntermediateField k L) : Submodule E V :=
  Submodule.span E (Set.range f)

private abbrev codRestrictRangeSpan (f : W →ₗ[k] V) (E : IntermediateField k L) :
    W →ₗ[k] (rangeSpan f E).restrictScalars k :=
  f.codRestrict ((rangeSpan f E).restrictScalars k) fun w ↦
    ((rangeSpan f E).restrictScalars_mem k _).mpr (Submodule.subset_span ⟨w, rfl⟩)

omit [IsScalarTower k L V] in
/-- For `f : W →ₗ[k] V` whose `L`-multiples transform semilinearly, `rangeSpan f E` is preserved
by `Gal(L/k)`, fixed pointwise by `E.fixingSubgroup`, and `E`-semilinear. -/
private theorem span_range_mem_and_fix {ρ : Representation k Gal(L/k) V}
    {f : W →ₗ[k] V} (hsemi : ∀ (g : Gal(L/k)) (a : L) (w : W), ρ g (a • f w) = g a • f w)
    (E : IntermediateField k L) [Normal k E] :
    (∀ (g : Gal(L/k)) ⦃u : V⦄, u ∈ rangeSpan f E → ρ g u ∈ rangeSpan f E) ∧
      (∀ ⦃g : Gal(L/k)⦄, g ∈ E.fixingSubgroup → ∀ ⦃u : V⦄, u ∈ rangeSpan f E → ρ g u = u) ∧
      (∀ (g : Gal(L/k)) (a : E) ⦃u : V⦄, u ∈ rangeSpan f E →
        ρ g (a • u) = AlgEquiv.restrictNormalHom E g a • ρ g u) := by
  have hfw (g : Gal(L/k)) (w : W) : ρ g (f w) = f w := by simpa using hsemi g 1 w
  refine span_mem_and_fix
    (by rintro g _ ⟨w, rfl⟩; exact (hfw g w).symm ▸ Submodule.subset_span ⟨w, rfl⟩)
    (by rintro g _ _ ⟨w, rfl⟩; exact hfw g w) ?_
  rintro g a _ ⟨w, rfl⟩
  rw [Subalgebra.smul_def, hsemi, ← AlgEquiv.restrictNormalHom_apply E g a, Subalgebra.smul_def,
    hfw]

/-- Reduce a single tensor `z : L ⊗[k] W` to a finite Galois subextension `E / k`: choose `E` and
`z₀ : E ⊗[k] W` mapping to `z`, build the descended `Gal(E/k)`-representation on `rangeSpan f E`,
and record the base-change comparison at `z₀`. -/
private theorem exists_finite_isGalois_descentRep [IsGalois k L]
    {ρ : Representation k Gal(L/k) V} {f : W →ₗ[k] V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (w : W), ρ g (a • f w) = g a • f w) (z : L ⊗[k] W) :
    ∃ (E : IntermediateField k L) (_ : FiniteDimensional k E) (_ : IsGalois k E)
      (z₀ : E ⊗[k] W)
      (ρE : Representation k Gal(E/k) ((rangeSpan f E).restrictScalars k)),
      LinearMap.rTensor W E.val.toLinearMap z₀ = z ∧
      ((codRestrictRangeSpan f E).liftBaseChange E z₀ : V) = f.liftBaseChange L z ∧
      (∀ (g : Gal(L/k)) (u : (rangeSpan f E).restrictScalars k),
        (ρE (AlgEquiv.restrictNormalHom E g) u : V) = ρ g u) ∧
      (∀ (σ : Gal(E/k)) (a : E) (u : (rangeSpan f E).restrictScalars k),
        ρE σ (a • u) = (σ • a) • ρE σ u) ∧
      (∀ (σ : Gal(E/k)) (w : W),
        ρE σ (codRestrictRangeSpan f E w) = codRestrictRangeSpan f E w) := by
  obtain ⟨E, hfin, hnorm, hzE⟩ :=
    Set.exists_normal_intermediateField_subset_range_rTensor {z} (Set.finite_singleton z)
  obtain ⟨z₀, rfl⟩ := hzE (Set.mem_singleton z)
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E L
  have hgal : IsGalois k E := ⟨⟩
  obtain ⟨hU_mem, hU_fix, hU_smul⟩ := span_range_mem_and_fix hsemi E
  let ρE := descentRep hU_mem hU_fix
  have hcomp :
      ((rangeSpan f E).restrictScalars k).subtype ∘ₗ
        ((codRestrictRangeSpan f E).liftBaseChange E).restrictScalars k =
      (f.liftBaseChange L).restrictScalars k ∘ₗ LinearMap.rTensor W E.val.toLinearMap :=
    TensorProduct.ext' fun a w ↦ by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.liftBaseChange_tmul, Submodule.coe_subtype, LinearMap.rTensor_tmul,
        IntermediateField.coe_val, AlgHom.toLinearMap_apply]
      -- `restrictScalars.origModule` inherits the `E`-action of `rangeSpan f E`.
      exact ((rangeSpan f E).coe_smul a _).trans <| by
        rw [LinearMap.codRestrict_apply, Subalgebra.smul_def]
  refine ⟨E, hfin, hgal, z₀, ρE, rfl, LinearMap.congr_fun hcomp z₀,
    descentRep_restrictNormalHom_coe hU_mem hU_fix,
    descentRep_smul hU_mem hU_fix hU_smul, fun σ w ↦ ?_⟩
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  refine Subtype.ext ((descentRep_restrictNormalHom_coe hU_mem hU_fix g _).trans ?_)
  rw [LinearMap.codRestrict_apply]
  simpa using hsemi g 1 w

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
  obtain ⟨E, _, _, z₀, ρE, rfl, hval, _, hρE_smul, hρE_f⟩ :=
    exists_finite_isGalois_descentRep hsemi z
  have hfE : Function.Injective (codRestrictRangeSpan f E) :=
    fun _ _ h ↦ hf (congrArg Subtype.val h)
  have hinj := liftBaseChange_injective_of_invariant (ρ := ρE) hfE fun σ a w ↦ by
    rw [hρE_smul, hρE_f]
  have hz₀ : z₀ = 0 := hinj <| by
    rw [map_zero]
    exact Subtype.ext (by rw [hval, hz, ZeroMemClass.coe_zero])
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
  obtain ⟨E, _, _, z₀, ρE, _, hval, hρE_coe, hρE_smul, hρE_f⟩ :=
    exists_finite_isGalois_descentRep (fun g a w ↦ by rw [hsemi, hinv]) z
  have hsurjE : Function.Surjective ((codRestrictRangeSpan f E).liftBaseChange E) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, eq_top_iff]
    rintro ⟨u, hu⟩ -
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, rfl⟩
    | zero => exact zero_mem _
    | add _ _ _ _ ihx ihy => exact add_mem ihx ihy
    | smul a _ _ ihx => exact Submodule.smul_mem _ a ihx
  let u₀ := (codRestrictRangeSpan f E).liftBaseChange E z₀
  have hu₀_inv : u₀ ∈ ρE.invariants := (ρE.mem_invariants u₀).mpr fun σ ↦ by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    exact Subtype.ext (by rw [hρE_coe, hval]; exact (ρ.mem_invariants _).mp hv g)
  rw [← range_eq_invariants_of_liftBaseChange_surjective hρE_smul hρE_f hsurjE] at hu₀_inv
  obtain ⟨w, hw⟩ := hu₀_inv
  exact ⟨w, (congrArg Subtype.val hw).trans hval⟩

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
  obtain ⟨hU_mem, hU_fix, hU_smul⟩ := span_mem_and_fix (E := E) (S := S)
    (by
      rintro σ _ ⟨g, rfl⟩
      rw [← mul_apply_eq_comp, ← map_mul]
      exact Submodule.subset_span ⟨σ * g, rfl⟩)
    (by
      rintro h hh _ ⟨g, rfl⟩
      have hconj : g⁻¹ * h * g ∈ E.fixingSubgroup := by
        rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker] at hh ⊢
        simp [hh]
      simpa [← mul_apply_eq_comp, ← map_mul, mul_assoc] using congrArg (ρ g) (hfix_v hconj))
    (by
      rintro σ a _ ⟨g, rfl⟩
      rw [Subalgebra.smul_def, hsemi, ← AlgEquiv.restrictNormalHom_apply E σ a,
        Subalgebra.smul_def])
  let ρE := descentRep hU_mem hU_fix
  have hspanE := span_invariants_eq_top (ρ := ρE) (descentRep_smul hU_mem hU_fix hU_smul)
  have hvU : (⟨v, Submodule.subset_span ⟨1, by simp⟩⟩ : U.restrictScalars k) ∈
      Submodule.span E (ρE.invariants : Set (U.restrictScalars k)) :=
    hspanE ▸ Submodule.mem_top
  suffices ∀ u ∈ Submodule.span E (ρE.invariants : Set (U.restrictScalars k)),
      (u : V) ∈ Submodule.span L (ρ.invariants : Set V) from this _ hvU
  intro u hu
  induction hu using Submodule.span_induction with
  | mem w hw =>
    refine Submodule.subset_span ((ρ.mem_invariants (w : V)).mpr fun g ↦ ?_)
    have hg := congrArg Subtype.val ((ρE.mem_invariants w).mp hw (AlgEquiv.restrictNormalHom E g))
    rwa [descentRep_restrictNormalHom_coe] at hg
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a _ _ hx => exact Submodule.smul_mem _ (a : L) hx

omit [IsScalarTower k L V] in
/-- The `L`-submodule of vectors in `V` whose stabilizer in `Gal(L/k)` is open for the Krull
topology under a semilinear representation `ρ`. -/
def openStabilizerSubmodule [Algebra.IsIntegral k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v) :
    Submodule L V where
  carrier := {v : V | IsOpen {g : Gal(L/k) | ρ g v = v}}
  zero_mem' := Subgroup.isOpen_mono (H₁ := ⊤) (H₂ := ρ.stabilizer 0)
    (ρ.stabilizer_zero ▸ le_rfl) isOpen_univ
  add_mem' {x y} hx hy := Subgroup.isOpen_mono (ρ.le_stabilizer_add x y) (hx.inter hy)
  smul_mem' c {x} hx := Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer Gal(L/k) c ⊓ ρ.stabilizer x) (H₂ := ρ.stabilizer (c • x))
    (fun g ⟨hgc, hgx⟩ ↦ (hsemi g c x).trans
      (by rw [← AlgEquiv.smul_def, MulAction.mem_stabilizer_iff.mp hgc, ρ.mem_stabilizer.mp hgx]))
    ((stabilizer_isOpen_of_isIntegral c).inter hx)

omit [IsScalarTower k L V] in
/-- Membership in `openStabilizerSubmodule hsemi` is openness of the stabilizer in `Gal(L/k)`. -/
@[simp]
theorem mem_openStabilizerSubmodule [Algebra.IsIntegral k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v) (v : V) :
    v ∈ openStabilizerSubmodule hsemi ↔ IsOpen {g : Gal(L/k) | ρ g v = v} :=
  Iff.rfl

omit [IsScalarTower k L V] in
/-- **Vectors spanned by invariants have open stabilizers.** Over an algebraic extension `L / k`,
if `V` is spanned over `L` by the invariants of a semilinear representation `ρ` of `Gal(L/k)` on
`V`, then every vector in `V` has an open stabilizer in `Gal(L/k)` for the Krull topology. -/
theorem isOpen_of_span_invariants_eq_top [Algebra.IsIntegral k L]
    {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v)
    (hspan : Submodule.span L (ρ.invariants : Set V) = ⊤) (v : V) :
    IsOpen {g : Gal(L/k) | ρ g v = v} := by
  refine (mem_openStabilizerSubmodule hsemi v).mp
    (Submodule.span_le.mpr ?_ (hspan ▸ Submodule.mem_top))
  intro x hx
  exact Subgroup.isOpen_mono (H₁ := ⊤) (H₂ := ρ.stabilizer x)
    (fun g _ ↦ (ρ.mem_invariants x).mp hx g) isOpen_univ

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
    fun g a w ↦ by rw [Submodule.coe_subtype, hsemi, (ρ.mem_invariants w.val).mp w.property g], ?_⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, Submodule.range_subtype,
    span_invariants_eq_top_of_isOpen hsemi hopen]

end TauCeti.GaloisDescent
