/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.RepresentationTheory.Pi.External
public import TauCeti.Topology.ImplicitAtlas.Basic

/-!
# Locally orientable implicit atlases

At a regular zero `x` of an implicit atlas, that is a point of `X_I^reg` where every Kuranishi map
`s_α`, `α ∈ I`, vanishes, two orientation lines meet: the local orientation line
`o_x = Hₙ(X_I, X_I ∖ {x}; ℤ)` of the regular locus, a topological manifold of dimension
`n = d + dim E_I`, and the orientation line `o_(E_I)` of the obstruction space
`E_I = ∏_(α ∈ I) E_α`. The stabilizer of `x` in `Γ_I` acts on both: on `o_x` through the
homeomorphisms of `X_I` it acts by, and on `o_(E_I)` by the sign of the determinant of its linear
action (`Representation.orientation_eq_sign_det_smul`). Pardon calls the atlas *locally
orientable* when every such stabilizer acts trivially on `o_x ⊗ o_(E_I)^∨`. This is the hypothesis
under which the orientation lines `o_x ⊗ o_(E_I)^∨` of the charts descend to a rank-one local
system on `X`, the virtual orientation sheaf in whose Čech cohomology the virtual fundamental
class lives.

Since the action on the dual line `o_(E_I)^∨` is by the same sign as on `o_(E_I)`, the condition
says that `g` acts on `o_x` by `sign (det ρ_I(g))`. This is the form of the definition
`TauCeti.ImplicitAtlas.IsLocallyOrientable`. The local homology is taken in `X_I`; by excision it
is the local homology of the open subset `X_I^reg` at `x`. The sign of `det ρ_I(g)` is the product
of the signs of `det ρ_α(g_α)` over `α ∈ I` (`Representation.det_externalPi`).

An atlas whose stabilizers at regular zeros are trivial is locally orientable
(`TauCeti.ImplicitAtlas.isLocallyOrientable_of_forall_eq_one`); in particular one with trivial
isotropy groups (`TauCeti.ImplicitAtlas.isLocallyOrientable_of_subsingleton`). The example atlases
of `TauCeti.Topology.ImplicitAtlas.Examples` are treated in
`TauCeti.Topology.ImplicitAtlas.LocallyOrientable.Examples`.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definitions 4.1.1 (orientation
  lines) and 4.1.2 (locally orientable implicit atlases).
-/

public section

open CategoryTheory Set

universe w

namespace TauCeti.ImplicitAtlas

variable {A : Type*} [DecidableEq A] {Γ : A → Type*} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type*} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type w} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type*} [TopologicalSpace X] {d : ℤ}

omit [DecidableEq A] [∀ α, Finite (Γ α)] [∀ I, T2Space (T I)] in
/-- An element of `Γ_I` fixing `x` sends no other point of `X_I` to `x`, so it induces a map of
the local homology of `X_I` at `x` to itself. -/
theorem act_preimage_singleton_subset {I : Finset A} {g : (α : I) → Γ α} {x : T I}
    (hg : act I g x = x) : ⇑(act I g : C(T I, T I)) ⁻¹' {x} ⊆ {x} :=
  fun _ hy ↦ (act I g).injective (hy.trans hg.symm)

/-- An implicit atlas is **locally orientable** (Pardon, Definition 4.1.2) when at every regular
zero `x ∈ X_I^reg ∩ s_I⁻¹(0)` the stabilizer of `x` in `Γ_I` acts trivially on
`o_x ⊗ o_(E_I)^∨`, where `o_x = Hₙ(X_I, X_I ∖ {x}; ℤ)` is the local orientation line of the
regular locus, of dimension `n = d + dim E_I`, and `o_(E_I)` the orientation line of
`E_I = ∏_(α ∈ I) E_α`. Equivalently, every `g` fixing `x` acts on `o_x` by the sign of the
determinant of its action on `E_I`, which is the sign by which it acts on `o_(E_I)` and on its
dual. -/
def IsLocallyOrientable (𝒜 : ImplicitAtlas Γ E ρ T act X d) : Prop :=
  ∀ (I : Finset A) (x : T I), x ∈ 𝒜.regLocus I → x ∈ kuranishiZeroSet 𝒜.kuranishi ∅ I →
    ∀ (g : (α : I) → Γ α) (hg : act I g x = x) (n : ℕ),
      (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) →
      localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (act I g : C(T I, T I))
          (act_preimage_singleton_subset hg) n =
        (SignType.sign (LinearMap.det (Representation.externalPi (fun α : I ↦ ρ α) g)) : ℤ) •
          𝟙 _

/-- The defining property of `TauCeti.ImplicitAtlas.IsLocallyOrientable`, for use in other files. -/
theorem isLocallyOrientable_iff {𝒜 : ImplicitAtlas Γ E ρ T act X d} :
    𝒜.IsLocallyOrientable ↔
      ∀ (I : Finset A) (x : T I), x ∈ 𝒜.regLocus I → x ∈ kuranishiZeroSet 𝒜.kuranishi ∅ I →
        ∀ (g : (α : I) → Γ α) (hg : act I g x = x) (n : ℕ),
          (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ) →
          localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (act I g : C(T I, T I))
              (act_preimage_singleton_subset hg) n =
            (SignType.sign (LinearMap.det (Representation.externalPi (fun α : I ↦ ρ α) g)) :
              ℤ) • 𝟙 _ :=
  Iff.rfl

/-- In a locally orientable atlas, an element `g` of `Γ_I` fixing a regular zero `x` acts on the
local orientation line `Hₙ(X_I, X_I ∖ {x}; ℤ)`, `n = d + dim E_I`, by the sign of the determinant
of its action on `E_I`. -/
theorem IsLocallyOrientable.localHomologyMap_eq {𝒜 : ImplicitAtlas Γ E ρ T act X d}
    (h : 𝒜.IsLocallyOrientable) {I : Finset A} {x : T I} (hx : x ∈ 𝒜.regLocus I)
    (hx₀ : x ∈ kuranishiZeroSet 𝒜.kuranishi ∅ I) {g : (α : I) → Γ α} (hg : act I g x = x)
    {n : ℕ} (hn : (n : ℤ) = d + ∑ α ∈ I, (Module.finrank ℝ (E α) : ℤ)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (act I g : C(T I, T I))
        (act_preimage_singleton_subset hg) n =
      (SignType.sign (LinearMap.det (Representation.externalPi (fun α : I ↦ ρ α) g)) : ℤ) •
        𝟙 _ :=
  h I x hx hx₀ g hg n hn

/-- An atlas whose stabilizers at regular zeros are trivial is locally orientable: the identity
acts trivially on every orientation line. -/
theorem isLocallyOrientable_of_forall_eq_one {𝒜 : ImplicitAtlas Γ E ρ T act X d}
    (h : ∀ (I : Finset A) (x : T I), x ∈ 𝒜.regLocus I →
      x ∈ kuranishiZeroSet 𝒜.kuranishi ∅ I → ∀ g : (α : I) → Γ α, act I g x = x → g = 1) :
    𝒜.IsLocallyOrientable := by
  refine isLocallyOrientable_iff.2 fun I x hx hx₀ g hg n _ ↦ ?_
  obtain rfl := h I x hx hx₀ g hg
  have hid : (act I 1 : C(T I, T I)) = ContinuousMap.id (T I) := by
    ext
    simp
  rw [map_one (Representation.externalPi fun α : I ↦ ρ α), map_one LinearMap.det, sign_one,
    SignType.coe_one, one_smul]
  exact localHomologyMap_eq_id _ hid _ n

/-- An atlas with trivial isotropy groups is locally orientable. -/
theorem isLocallyOrientable_of_subsingleton [∀ α, Subsingleton (Γ α)]
    (𝒜 : ImplicitAtlas Γ E ρ T act X d) : 𝒜.IsLocallyOrientable :=
  isLocallyOrientable_of_forall_eq_one fun _ _ _ _ _ _ ↦ Subsingleton.elim _ _

end TauCeti.ImplicitAtlas
