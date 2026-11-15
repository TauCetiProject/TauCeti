/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.RepresentationTheory.GaloisDescent.Injective
import TauCeti.RepresentationTheory.GaloisDescent.Range
import TauCeti.RepresentationTheory.GaloisDescent.Span

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

section Helpers

variable {k L V W : Type*} [Field k] [Field L] [Algebra k L]

/-- Every element of `L ⊗[k] W` over a normal algebraic extension `L / k` comes from `E ⊗[k] W` for
some finite normal intermediate field `E / k`. -/
private theorem exists_normal_intermediateField_rTensor_eq [AddCommGroup W] [Module k W]
    [Algebra.IsIntegral k L] [Normal k L] (z : L ⊗[k] W) :
    ∃ (E : IntermediateField k L), FiniteDimensional k E ∧ Normal k E ∧
      ∃ z₀ : E ⊗[k] W, LinearMap.rTensor W E.val.toLinearMap z₀ = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a w =>
    have : FiniteDimensional k k⟮a⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
    let E := normalClosure k k⟮a⟯ L
    have ha : a ∈ E := k⟮a⟯.le_normalClosure (IntermediateField.mem_adjoin_simple_self k a)
    exact ⟨E, normalClosure.is_finiteDimensional k _ L, normalClosure.normal k _ L,
      ⟨a, ha⟩ ⊗ₜ[k] w, rfl⟩
  | add x y hx hy =>
    obtain ⟨E₁, hfin₁, _, z₁, rfl⟩ := hx
    obtain ⟨E₂, hfin₂, _, z₂, rfl⟩ := hy
    have : FiniteDimensional k (E₁ ⊔ E₂ : IntermediateField k L) :=
      IntermediateField.finiteDimensional_sup E₁ E₂
    let E := normalClosure k (E₁ ⊔ E₂ : IntermediateField k L) L
    have h₁ : E₁ ≤ E := le_sup_left.trans (E₁ ⊔ E₂).le_normalClosure
    have h₂ : E₂ ≤ E := le_sup_right.trans (E₁ ⊔ E₂).le_normalClosure
    refine ⟨E, normalClosure.is_finiteDimensional k _ L, normalClosure.normal k _ L,
      LinearMap.rTensor W (inclusion h₁).toLinearMap z₁ +
        LinearMap.rTensor W (inclusion h₂).toLinearMap z₂, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← LinearMap.rTensor_comp]
    rfl

/-- The `k`-submodule of `V` consisting of `E`-linear combinations of elements of `S`. -/
private def spanE [AddCommGroup V] [Module k V] [Module L V]
    (E : IntermediateField k L) (S : Set V) : Submodule k V :=
  Submodule.span k {v : V | ∃ a : E, ∃ s ∈ S, (a : L) • s = v}

private theorem mem_spanE_of_mem [AddCommGroup V] [Module k V] [Module L V]
    {E : IntermediateField k L} {S : Set V} {s : V} (hs : s ∈ S) :
    s ∈ spanE E S :=
  Submodule.subset_span ⟨1, s, hs, one_smul L s⟩

private theorem smul_mem_spanE [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
    {E : IntermediateField k L} {S : Set V} (a : E) {u : V}
    (hu : u ∈ spanE E S) : (a : L) • u ∈ spanE E S := by
  induction hu using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨b, s, hs, rfl⟩ := hx
    exact Submodule.subset_span ⟨a * b, s, hs, by rw [MulMemClass.coe_mul, mul_smul]⟩
  | zero =>
    rw [smul_zero]
    exact zero_mem _
  | add _ _ _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul c _ _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hx

/-- The `E`-module structure on `spanE E S` inherited from the `L`-module structure on `V`. -/
@[instance_reducible]
private def spanEModule [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
    (E : IntermediateField k L) (S : Set V) : Module E (spanE E S) where
  smul a u := ⟨(a : L) • u.1, smul_mem_spanE a u.2⟩
  one_smul u := Subtype.ext (one_smul L u.1)
  mul_smul a b u := Subtype.ext (mul_smul (a : L) (b : L) u.1)
  smul_zero a := Subtype.ext (smul_zero (a : L))
  smul_add a u₁ u₂ := Subtype.ext (smul_add (a : L) u₁.1 u₂.1)
  add_smul a b u := Subtype.ext (add_smul (a : L) (b : L) u.1)
  zero_smul u := Subtype.ext (zero_smul L u.1)

private theorem coe_spanE_smul [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
    (E : IntermediateField k L) (S : Set V) (a : E) (u : spanE E S) :
    letI := spanEModule E S
    ((a • u : spanE E S) : V) = (a : L) • (u : V) :=
  rfl

private theorem isScalarTower_spanE [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
    (E : IntermediateField k L) (S : Set V) :
    letI := spanEModule E S
    IsScalarTower k E (spanE E S) :=
  letI := spanEModule E S
  ⟨fun c a u ↦ Subtype.ext (smul_assoc c (a : L) u.1)⟩

/-- Compatibility between `liftBaseChange E` into `spanE E (Set.range f)` and `liftBaseChange L`. -/
private theorem subtype_comp_liftBaseChange_codRestrict [AddCommGroup V] [Module k V] [Module L V]
    [IsScalarTower k L V] [AddCommGroup W] [Module k W] (E : IntermediateField k L)
    (f : W →ₗ[k] V) :
    letI := spanEModule E (Set.range f)
    haveI := isScalarTower_spanE E (Set.range f)
    (spanE E (Set.range f)).subtype.comp
        (((f.codRestrict (spanE E (Set.range f)) fun w ↦
          mem_spanE_of_mem ⟨w, rfl⟩).liftBaseChange E).restrictScalars k) =
      ((f.liftBaseChange L).restrictScalars k).comp (LinearMap.rTensor W E.val.toLinearMap) := by
  let := spanEModule E (Set.range f)
  have := isScalarTower_spanE E (Set.range f)
  refine TensorProduct.ext' fun a w ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul,
    LinearMap.rTensor_tmul, AlgHom.coe_toLinearMap]
  rfl

/-- Lifting `AlgEquiv.restrictNormalHom E g` back to `Gal(L/k)` via `AlgEquiv.liftNormal L` gives
the same action on `U` whenever `E.fixingSubgroup` fixes `U` pointwise. -/
private theorem liftNormal_restrictNormalHom_apply [AddCommGroup V] [Module k V] [Normal k L]
    {ρ : Representation k Gal(L/k) V} (E : IntermediateField k L) [Normal k E] {U : Submodule k V}
    (hU_fix : ∀ {g : Gal(L/k)}, g ∈ E.fixingSubgroup → ∀ {u : V}, u ∈ U → ρ g u = u)
    (g : Gal(L/k)) {u : V} (hu : u ∈ U) :
    ρ ((AlgEquiv.restrictNormalHom E g).liftNormal L) u = ρ g u := by
  have hmem : ((AlgEquiv.restrictNormalHom E g).liftNormal L)⁻¹ * g ∈ E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact (AlgEquiv.restrictNormalHom E g).restrict_liftNormal L
  have h := congrArg (ρ ((AlgEquiv.restrictNormalHom E g).liftNormal L)) (hU_fix hmem hu)
  simpa [← mul_apply_eq_comp, ← map_mul] using h.symm

/-- Given a normal intermediate field `E` of `L / k` and a `k`-submodule `U` of `V` preserved by
`ρ` and fixed pointwise by `E.fixingSubgroup`, `ρ` descends along restriction to a representation
of `Gal(E/k)` on `U`. -/
private noncomputable def descendToNormal [AddCommGroup V] [Module k V] [Normal k L]
    {ρ : Representation k Gal(L/k) V} (E : IntermediateField k L) [Normal k E] (U : Submodule k V)
    (hU_mem : ∀ (g : Gal(L/k)) {u : V}, u ∈ U → ρ g u ∈ U)
    (hU_fix : ∀ {g : Gal(L/k)}, g ∈ E.fixingSubgroup → ∀ {u : V}, u ∈ U → ρ g u = u) :
    Representation k Gal(E/k) U where
  toFun σ := (ρ (σ.liftNormal L)).restrict fun _ hu ↦ hU_mem (σ.liftNormal L) hu
  map_one' := LinearMap.ext fun u ↦ Subtype.ext <| by
    have h := liftNormal_restrictNormalHom_apply E hU_fix 1 u.2
    simpa [LinearMap.restrict_apply] using h
  map_mul' σ τ := LinearMap.ext fun u ↦ Subtype.ext <| by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L τ
    simp only [← map_mul, mul_apply_eq_comp, LinearMap.restrict_apply]
    rw [liftNormal_restrictNormalHom_apply E hU_fix (g * h) u.2,
      liftNormal_restrictNormalHom_apply E hU_fix h u.2,
      liftNormal_restrictNormalHom_apply E hU_fix g (hU_mem h u.2), map_mul, mul_apply_eq_comp]

private theorem coe_descendToNormal_restrictNormalHom [AddCommGroup V] [Module k V] [Normal k L]
    {ρ : Representation k Gal(L/k) V} (E : IntermediateField k L) [Normal k E]
    (U : Submodule k V) (hU_mem : ∀ (g : Gal(L/k)) {u : V}, u ∈ U → ρ g u ∈ U)
    (hU_fix : ∀ {g : Gal(L/k)}, g ∈ E.fixingSubgroup → ∀ {u : V}, u ∈ U → ρ g u = u)
    (g : Gal(L/k)) (u : U) :
    (descendToNormal E U hU_mem hU_fix (AlgEquiv.restrictNormalHom E g) u : V) = ρ g u :=
  liftNormal_restrictNormalHom_apply E hU_fix g u.2

/-- A semilinear representation of `Gal(L/k)` descends to a semilinear representation of `Gal(E/k)`
on `spanE E S`. -/
private theorem descendToNormal_smul [AddCommGroup V] [Module k V] [Module L V]
    [IsScalarTower k L V] [Normal k L] {ρ : Representation k Gal(L/k) V}
    (hsemi : ∀ (g : Gal(L/k)) (a : L) (v : V), ρ g (a • v) = g a • ρ g v)
    (E : IntermediateField k L) [Normal k E] (S : Set V)
    (hU_mem : ∀ (g : Gal(L/k)) {u : V}, u ∈ spanE E S → ρ g u ∈ spanE E S)
    (hU_fix : ∀ {g : Gal(L/k)}, g ∈ E.fixingSubgroup → ∀ {u : V}, u ∈ spanE E S → ρ g u = u)
    (σ : Gal(E/k)) (a : E) (u : spanE E S) :
    letI := spanEModule E S
    descendToNormal E (spanE E S) hU_mem hU_fix σ (a • u) =
      (σ • a) • descendToNormal E (spanE E S) hU_mem hU_fix σ u := by
  let := spanEModule E S
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
  apply Subtype.ext
  rw [coe_descendToNormal_restrictNormalHom, coe_spanE_smul, coe_spanE_smul,
    coe_descendToNormal_restrictNormalHom, hsemi, ← AlgEquiv.restrictNormalHom_apply E g a]
  rfl

/-- For `f : W →ₗ[k] V` whose `L`-multiples transform semilinearly, `spanE E (Set.range f)` is
preserved by `Gal(L/k)` and fixed pointwise by `E.fixingSubgroup`. -/
private theorem spanE_range_mem_and_fix [AddCommGroup V] [Module k V] [Module L V]
    [IsScalarTower k L V] [AddCommGroup W] [Module k W] {ρ : Representation k Gal(L/k) V}
    {f : W →ₗ[k] V} (hsemi : ∀ (g : Gal(L/k)) (a : L) (w : W), ρ g (a • f w) = g a • f w)
    (E : IntermediateField k L) [Normal k E] :
    (∀ (g : Gal(L/k)) {u : V}, u ∈ spanE E (Set.range f) → ρ g u ∈ spanE E (Set.range f)) ∧
      (∀ {g : Gal(L/k)}, g ∈ E.fixingSubgroup →
        ∀ {u : V}, u ∈ spanE E (Set.range f) → ρ g u = u) := by
  refine ⟨fun g {u} hu ↦ ?_, fun {g} hg {u} hu ↦ ?_⟩
  · induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨a, _, ⟨w, rfl⟩, rfl⟩ := hx
      rw [hsemi, ← AlgEquiv.restrictNormalHom_apply E g a]
      exact smul_mem_spanE (AlgEquiv.restrictNormalHom E g a) (mem_spanE_of_mem ⟨w, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c _ _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨a, _, ⟨w, rfl⟩, rfl⟩ := hx
      rw [hsemi, (mem_fixingSubgroup_iff E g).mp hg a a.2]
    | zero => exact map_zero _
    | add _ _ _ _ hx hy => rw [map_add, hx, hy]
    | smul c _ _ hx => rw [map_smul, hx]

end Helpers

section Descent

variable {k L V W : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
variable [AddCommGroup W] [Module k W]

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
  obtain ⟨E, hfin, hnorm, z₀, rfl⟩ := exists_normal_intermediateField_rTensor_eq z
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E L
  have : IsGalois k E := ⟨⟩
  let U := spanE E (Set.range f)
  let : Module E U := spanEModule E (Set.range f)
  have : IsScalarTower k E U := isScalarTower_spanE E (Set.range f)
  obtain ⟨hU_mem, hU_fix⟩ := spanE_range_mem_and_fix hsemi E
  let ρE : Representation k Gal(E/k) U := descendToNormal E U hU_mem hU_fix
  let fE : W →ₗ[k] U := f.codRestrict U fun w ↦ mem_spanE_of_mem ⟨w, rfl⟩
  have hfE : Function.Injective fE := fun w₁ w₂ h ↦ hf (congrArg Subtype.val h)
  have hsemiE (σ : Gal(E/k)) (a : E) (w : W) : ρE σ (a • fE w) = (σ • a) • fE w := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    apply Subtype.ext
    rw [coe_descendToNormal_restrictNormalHom, coe_spanE_smul, coe_spanE_smul]
    exact (hsemi g (a : L) w).trans (by rw [← AlgEquiv.restrictNormalHom_apply E g a]; rfl)
  have hinj := liftBaseChange_injective_of_invariant (ρ := ρE) hfE hsemiE
  have hcomp := subtype_comp_liftBaseChange_codRestrict E f
  have hz₀ : z₀ = 0 := by
    refine hinj ?_
    rw [map_zero]
    exact Subtype.ext (by simpa [fE, hz] using LinearMap.congr_fun hcomp z₀)
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
  obtain ⟨E, hfin, hnorm, z₀, rfl⟩ := exists_normal_intermediateField_rTensor_eq z
  have : Algebra.IsSeparable k E := Algebra.isSeparable_tower_bot_of_isSeparable k E L
  have : IsGalois k E := ⟨⟩
  let U := spanE E (Set.range f)
  let : Module E U := spanEModule E (Set.range f)
  have : IsScalarTower k E U := isScalarTower_spanE E (Set.range f)
  have hsemi' (g : Gal(L/k)) (a : L) (w : W) : ρ g (a • f w) = g a • f w := by
    rw [hsemi, hinv]
  obtain ⟨hU_mem, hU_fix⟩ := spanE_range_mem_and_fix hsemi' E
  let ρE : Representation k Gal(E/k) U := descendToNormal E U hU_mem hU_fix
  let fE : W →ₗ[k] U := f.codRestrict U fun w ↦ mem_spanE_of_mem ⟨w, rfl⟩
  have hsemiE := descendToNormal_smul hsemi E (Set.range f) hU_mem hU_fix
  have hinvE (σ : Gal(E/k)) (w : W) : ρE σ (fE w) = fE w := by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    exact Subtype.ext ((coe_descendToNormal_restrictNormalHom E U hU_mem hU_fix g (fE w)).trans
      (hinv g w))
  have hsurjE : Function.Surjective (fE.liftBaseChange E) := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro ⟨u, hu⟩ -
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨a, _, ⟨w, rfl⟩, rfl⟩ := hx
      exact ⟨a ⊗ₜ[k] w, Subtype.ext rfl⟩
    | zero => exact zero_mem (LinearMap.range (fE.liftBaseChange E))
    | add _ _ _ _ ihx ihy => exact add_mem ihx ihy
    | smul c x hx ihx =>
      have hc : (⟨c • x, U.smul_mem c hx⟩ : U) = (algebraMap k E c) • (⟨x, hx⟩ : U) :=
        Subtype.ext (IsScalarTower.algebraMap_smul L c x).symm
      exact hc ▸ (LinearMap.range (fE.liftBaseChange E)).smul_mem (algebraMap k E c) ihx
  let u₀ : U := fE.liftBaseChange E z₀
  have hu₀_val : (u₀ : V) = f.liftBaseChange L (LinearMap.rTensor W E.val.toLinearMap z₀) :=
    LinearMap.congr_fun (subtype_comp_liftBaseChange_codRestrict E f) z₀
  have hu₀_inv : u₀ ∈ ρE.invariants := (ρE.mem_invariants u₀).mpr fun σ ↦ by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L σ
    exact Subtype.ext <| (coe_descendToNormal_restrictNormalHom E U hU_mem hU_fix g u₀).trans <| by
      rw [hu₀_val, (ρ.mem_invariants _).mp hv g]
  rw [← range_eq_invariants_of_liftBaseChange_surjective hsemiE hinvE hsurjE] at hu₀_inv
  obtain ⟨w, hw⟩ := hu₀_inv
  exact ⟨w, (congrArg Subtype.val hw).trans hu₀_val⟩

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
  let S : Set V := Set.range fun g : Gal(L/k) ↦ ρ g v
  let U := spanE E S
  let : Module E U := spanEModule E S
  have hU_mem (σ : Gal(L/k)) {u : V} (hu : u ∈ U) : ρ σ u ∈ U := by
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨a, _, ⟨g, rfl⟩, rfl⟩ := hx
      rw [hsemi, ← mul_apply_eq_comp, ← map_mul, ← AlgEquiv.restrictNormalHom_apply E σ a]
      exact smul_mem_spanE (AlgEquiv.restrictNormalHom E σ a) (mem_spanE_of_mem ⟨σ * g, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c _ _ hx => rw [map_smul]; exact U.smul_mem c hx
  have hU_fix {h : Gal(L/k)} (hh : h ∈ E.fixingSubgroup) {u : V} (hu : u ∈ U) :
      ρ h u = u := by
    induction hu using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨a, _, ⟨g, rfl⟩, rfl⟩ := hx
      have hconj : g⁻¹ * h * g ∈ E.fixingSubgroup := by
        rw [← E.restrictNormalHom_ker, MonoidHom.mem_ker] at hh ⊢
        simp [hh]
      have hv' : ρ (g⁻¹ * h * g) v = v := hfix_v hconj
      have hgv : ρ h (ρ g v) = ρ g v := by
        have := congrArg (ρ g) hv'
        simpa [← mul_apply_eq_comp, ← map_mul, mul_assoc] using this
      rw [hsemi, (mem_fixingSubgroup_iff E h).mp hh a a.2, hgv]
    | zero => exact map_zero _
    | add _ _ _ _ hx hy => rw [map_add, hx, hy]
    | smul c _ _ hx => rw [map_smul, hx]
  let ρE : Representation k Gal(E/k) U := descendToNormal E U hU_mem hU_fix
  have hsemiE := descendToNormal_smul hsemi E S hU_mem hU_fix
  have hspanE := span_invariants_eq_top (ρ := ρE) hsemiE
  let vU : U := ⟨v, mem_spanE_of_mem ⟨1, by simp⟩⟩
  have hvU : vU ∈ Submodule.span E (ρE.invariants : Set U) :=
    hspanE ▸ Submodule.mem_top
  have hval (u : U) (hu : u ∈ Submodule.span E (ρE.invariants : Set U)) :
      (u : V) ∈ Submodule.span L (ρ.invariants : Set V) := by
    induction hu using Submodule.span_induction with
    | mem w hw =>
      refine Submodule.subset_span ((ρ.mem_invariants (w : V)).mpr fun g ↦ ?_)
      rw [← coe_descendToNormal_restrictNormalHom E U hU_mem hU_fix g w]
      exact congrArg Subtype.val ((ρE.mem_invariants w).mp hw (AlgEquiv.restrictNormalHom E g))
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | smul a w _ hx =>
      rw [coe_spanE_smul]
      exact Submodule.smul_mem _ (a : L) hx
  exact hval vU hvU

omit [IsScalarTower k L V] in
/-- **Vectors spanned by invariants have open stabilizers.** Over an algebraic extension `L / k`,
if `V` is spanned over `L` by the invariants of a semilinear representation `ρ` of `Gal(L/k)`, then
every vector in `V` has an open stabilizer in `Gal(L/k)` for the Krull topology. -/
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
      (fun g ⟨hga, hgx⟩ ↦ (hsemi g a x).trans (by rw [show g a = a from hga, hgx]))
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
  rw [← LinearMap.range_eq_top]
  refine top_unique ?_
  rw [← span_invariants_eq_top_of_isOpen hsemi hopen, Submodule.span_le]
  intro x hx
  exact ⟨1 ⊗ₜ[k] ⟨x, hx⟩, by simp⟩

end Descent

end TauCeti.GaloisDescent
