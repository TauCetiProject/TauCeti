/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.StableLattice

/-!
# Integral models of continuous representations

Let `ρ` be a jointly continuous representation (`TauCeti.ContinuousRep`) of a topological monoid
`Γ` on a module `V` over a ring `E`, and let `O → E` be a ring map, typically the inclusion of a
discrete valuation ring into its fraction field. An *integral model* of `ρ` over `O` is a
`Γ`-stable full lattice `Λ ⊆ V`: a finitely generated `O`-submodule spanning `V` over `E`
(Mathlib's `Submodule.IsLattice E Λ`) and preserved by every `ρ g`. For an `ℓ`-adic Galois
representation on a `ℚ_ℓ`-vector space, an integral model is a `Γ`-stable `ℤ_ℓ`-lattice, the
object whose reductions modulo `ℓⁿ` are the finite-level Galois representations.

This file develops the elementary theory of integral models.

* `Γ` acts on `Λ` by restriction (`TauCeti.GaloisLattice.IntegralModel.toContinuousRep`), jointly
  continuously for the subspace topology.
* Scalar extension recovers the given representation: for a domain `O` with fraction field `E`
  and `Λ` free, `E ⊗[O] Λ ≅ V` equivariantly through the rationalization equivalence
  `Submodule.rationalizationEquiv` (`TauCeti.GaloisLattice.IntegralModel.genericFiberIso`). This
  is stated for `Λ` with its `O`-module topology; over the valuation ring of a field with a
  valuative topology, such as a nonarchimedean local field, the subspace topology on a lattice is
  its module topology (`Submodule.IsLattice.isModuleTopology`), and the valuation ring of a
  nonarchimedean local field is a discrete valuation ring, so every lattice there is free.
* The units of `E` act on integral models by homothety, and integral models are ordered by
  inclusion, with sums and, over a principal ideal domain with fraction field `E` and
  finite-dimensional `V`, intersections.
* A representation of a compact group on a finite-dimensional vector space over a field with a
  valuative topology, such as a nonarchimedean local field, has an integral model over the
  valuation ring (`TauCeti.GaloisLattice.IntegralModel.nonempty`), by the stable-lattice theorem.
* Over a discrete valuation ring with fraction field `E`, any two integral models are
  commensurable: `𝔪ᵃ Λ ⊆ Λ'` and `𝔪ᵃ Λ' ⊆ Λ` for some `a`
  (`TauCeti.GaloisLattice.IntegralModel.exists_pow_le`).

## Main definitions

* `TauCeti.GaloisLattice.IntegralModel O ρ`: the integral models of `ρ` over `O`.
* `TauCeti.GaloisLattice.IntegralModel.toContinuousRep`: the restricted action of `Γ` on `Λ`.
* `TauCeti.GaloisLattice.IntegralModel.genericFiberIso`: the equivariant identification of the
  scalar extension `E ⊗[O] Λ` with `V`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, paragraph after
  Proposition 2.6.
-/

public section

open Module Submodule
open scoped Pointwise TensorProduct

namespace TauCeti.GaloisLattice

section Basic

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] (O : Type*) [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E] {V : Type*} [AddCommGroup V] [Module E V] [Module O V]
  [IsScalarTower O E V] [TopologicalSpace V]

/-- **An integral model** of a continuous representation `ρ` of `Γ` on `V` over the coefficient
ring `O`: a full `O`-lattice in `V` (finitely generated over `O` and spanning `V` over `E`) that
is stable under every `ρ g`. -/
@[ext]
structure IntegralModel (ρ : ContinuousRep Γ E V) where
  /-- The underlying lattice. -/
  lattice : Submodule O V
  /-- The lattice is full: finitely generated over `O` and spanning `V` over `E`. -/
  isLattice : lattice.IsLattice E
  /-- The lattice is stable under the action. -/
  stable : ∀ g, ∀ x ∈ lattice, ρ g x ∈ lattice

attribute [instance] IntegralModel.isLattice

namespace IntegralModel

variable {O} {ρ : ContinuousRep Γ E V}

/-- An integral model is determined by its lattice. -/
theorem lattice_injective : Function.Injective (lattice : IntegralModel O ρ → Submodule O V) :=
  fun _ _ ↦ IntegralModel.ext

/-! ### The restricted action -/

/-- **The restriction of `ρ` to an integral model.** `Γ` acts `O`-linearly on the lattice `Λ`,
and the action is jointly continuous for the subspace topology on `Λ`. -/
def toContinuousRep (Λ : IntegralModel O ρ) : ContinuousRep Γ O Λ.lattice where
  toRepresentation :=
    { toFun g :=
        { toFun x := ⟨ρ g x, Λ.stable g x x.2⟩
          map_add' x y := Subtype.ext (map_add (ρ g) (x : V) y)
          map_smul' a x := Subtype.ext ((ρ g).map_smul_of_tower a (x : V)) }
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }
  continuous_action := (ρ.continuous_action.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The inclusion of an integral model intertwines its action with the action on `V`. -/
@[simp]
theorem coe_toContinuousRep_apply (Λ : IntegralModel O ρ) (g : Γ) (x : Λ.lattice) :
    (Λ.toContinuousRep g x : V) = ρ g x :=
  (rfl)

/-! ### Homotheties -/

/-- The units of `E` act on integral models by homothety, `c • Λ`. -/
instance : MulAction Eˣ (IntegralModel O ρ) where
  smul c Λ :=
    { lattice := c • Λ.lattice
      isLattice := inferInstance
      stable g x hx := by
        obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists x c Λ.lattice).mp hx
        rw [LinearMap.map_smul_of_tower]
        exact smul_mem_pointwise_smul _ c _ (Λ.stable g y hy) }
  one_smul Λ := IntegralModel.ext (one_smul _ Λ.lattice)
  mul_smul c d Λ := IntegralModel.ext (mul_smul c d Λ.lattice)

@[simp]
theorem lattice_smul (c : Eˣ) (Λ : IntegralModel O ρ) : (c • Λ).lattice = c • Λ.lattice :=
  (rfl)

/-! ### Inclusion, sums and intersections -/

instance : LE (IntegralModel O ρ) where
  le Λ Λ' := Λ.lattice ≤ Λ'.lattice

instance : LT (IntegralModel O ρ) where
  lt Λ Λ' := Λ.lattice < Λ'.lattice

@[simp]
theorem lattice_le_lattice {Λ Λ' : IntegralModel O ρ} : Λ.lattice ≤ Λ'.lattice ↔ Λ ≤ Λ' :=
  .rfl

@[simp]
theorem lattice_lt_lattice {Λ Λ' : IntegralModel O ρ} : Λ.lattice < Λ'.lattice ↔ Λ < Λ' :=
  .rfl

/-- The sum `Λ + Λ'` of two integral models. -/
instance : Max (IntegralModel O ρ) where
  max Λ Λ' :=
    { lattice := Λ.lattice ⊔ Λ'.lattice
      isLattice := inferInstance
      stable g x hx := by
        obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
        rw [map_add]
        exact add_mem (mem_sup_left (Λ.stable g y hy)) (mem_sup_right (Λ'.stable g z hz)) }

@[simp]
theorem lattice_sup (Λ Λ' : IntegralModel O ρ) : (Λ ⊔ Λ').lattice = Λ.lattice ⊔ Λ'.lattice :=
  (rfl)

instance : SemilatticeSup (IntegralModel O ρ) :=
  lattice_injective.semilatticeSup _ .rfl .rfl lattice_sup

end IntegralModel

end Basic

section Inf

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O] [IsDomain O]
  [IsPrincipalIdealRing O] {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  [FiniteDimensional E V] {ρ : ContinuousRep Γ E V}

namespace IntegralModel

/-- The intersection `Λ ∩ Λ'` of two integral models over a principal ideal domain with fraction
field `E`. -/
instance : Min (IntegralModel O ρ) where
  min Λ Λ' :=
    { lattice := Λ.lattice ⊓ Λ'.lattice
      isLattice := inferInstance
      stable g x hx := ⟨Λ.stable g x hx.1, Λ'.stable g x hx.2⟩ }

@[simp]
theorem lattice_inf (Λ Λ' : IntegralModel O ρ) : (Λ ⊓ Λ').lattice = Λ.lattice ⊓ Λ'.lattice :=
  (rfl)

instance : Lattice (IntegralModel O ρ) :=
  lattice_injective.lattice _ .rfl .rfl lattice_sup lattice_inf

end IntegralModel

end Inf

section GenericFiber

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O] [IsDomain O]
  [TopologicalSpace O] {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  [TopologicalSpace E] [IsTopologicalSemiring E] [ContinuousSMul O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  [IsModuleTopology E V] {ρ : ContinuousRep Γ E V}

namespace IntegralModel

variable (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice] [IsModuleTopology O Λ.lattice]
  [TopologicalSpace (E ⊗[O] Λ.lattice)] [IsModuleTopology E (E ⊗[O] Λ.lattice)]

/-- **The generic fibre of an integral model.** Extending scalars from `O` to its fraction field
`E` recovers the representation: `E ⊗[O] Λ ≅ V`, sending `a ⊗ x` to `a • x`. -/
noncomputable def genericFiberIso : ContinuousRep.Iso (Λ.toContinuousRep.baseChange E) ρ :=
  .ofEquiv (.mk (rationalizationEquiv Λ.lattice) fun g ↦ by
    ext x
    simp)

@[simp]
theorem genericFiberIso_tmul (a : E) (x : Λ.lattice) :
    Λ.genericFiberIso (a ⊗ₜ x) = a • (x : V) := by
  simp [genericFiberIso]

@[simp]
theorem genericFiberIso_symm_coe (x : Λ.lattice) :
    Λ.genericFiberIso.symm (x : V) = 1 ⊗ₜ x :=
  EquivLike.injective Λ.genericFiberIso <| by simp

end IntegralModel

end GenericFiber

section Existence

open ValuativeRel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
  {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsValuativeTopology E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]

/-- **Existence of integral models.** A jointly continuous representation of a compact group on a
finite-dimensional vector space over a field with a valuative topology, for instance a
nonarchimedean local field, has an integral model over the valuation ring `𝒪[E]`. -/
instance IntegralModel.nonempty (ρ : ContinuousRep Γ E V) : Nonempty (IntegralModel 𝒪[E] ρ) :=
  let ⟨L, hL, hρL⟩ := ρ.exists_stable_lattice
  ⟨⟨L, hL, hρL⟩⟩

end Existence

section Commensurable

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [TopologicalSpace V]
  {ρ : ContinuousRep Γ E V}

/-- **Integral models are commensurable.** Over a discrete valuation ring `O` with fraction field
`E`, any two integral models `Λ`, `Λ'` satisfy `𝔪ᵃ Λ ⊆ Λ'` and `𝔪ᵃ Λ' ⊆ Λ` for some `a`, where
`𝔪` is the maximal ideal of `O`. -/
theorem IntegralModel.exists_pow_le (Λ Λ' : IntegralModel O ρ) :
    ∃ a : ℕ, IsLocalRing.maximalIdeal O ^ a • Λ.lattice ≤ Λ'.lattice ∧
      IsLocalRing.maximalIdeal O ^ a • Λ'.lattice ≤ Λ.lattice := by
  obtain ⟨m, hm⟩ := IsLattice.exists_maximalIdeal_pow_smul_le E Λ'.lattice
    (IsLattice.fg (A := E) (M := Λ.lattice))
  obtain ⟨n, hn⟩ := IsLattice.exists_maximalIdeal_pow_smul_le E Λ.lattice
    (IsLattice.fg (A := E) (M := Λ'.lattice))
  -- Powers of the maximal ideal decrease, so `a = max m n` works in both directions.
  refine ⟨max m n, (smul_mono_left ?_).trans hm, (smul_mono_left ?_).trans hn⟩ <;>
    exact Ideal.pow_le_pow_right (by omega)

end Commensurable

end TauCeti.GaloisLattice
