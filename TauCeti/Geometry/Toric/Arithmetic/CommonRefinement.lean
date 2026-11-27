/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Face.Comap
public import TauCeti.Geometry.Convex.Cone.Face.Finite
public import TauCeti.Geometry.Toric.Algebraic.Cone.RationalDuality
public import TauCeti.Geometry.Toric.Arithmetic.Fan
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Common refinements of arithmetic cone systems

Toroidal compactifications attached to two cone systems, or to the source and target of a Hecke
or level-changing map, are compared through a common refinement. Let `Φ` be an arithmetic cone
system for the lattice `i : N →+ V`, the group `Γ`, the positivity cone `C` and its rational
closure `Cstar`, and let `Ψ` be one for `i' : N' →+ V'`, `Γ'`, `C'` and `Cstar'`. Let
`g : V →ₗ[ℝ] V'` be a real-linear map such that

* `g` carries lattice points to lattice points (`g ∘ i = i' ∘ f` for an additive `f : N →+ N'`);
* `g` carries the open positivity cone `C` into `C'`;
* `g` is equivariant: for each `γ ∈ Γ` there is `γ' ∈ Γ'` with `g ∘ γ = γ' ∘ g`;
* (finite relative overlap) for each cone `σ` of `Φ`, the intersections `σ ⊓ g⁻¹(τ)` with the
  cones `τ` of `Ψ` take only finitely many values.

Then the cones `σ ⊓ g⁻¹(τ)`, for `σ ∈ Φ` and `τ ∈ Ψ`, form an arithmetic cone system for `Γ`,
`TauCeti.Toric.ArithmeticFan.commonRefinement`. It is closed under faces because every face of
`σ ⊓ g⁻¹(τ)` is `σ' ⊓ g⁻¹(τ')` for faces `σ'` of `σ` and `τ'` of `τ`
(`PointedCone.IsFaceOf.exists_inf_comap_eq`), and it has finitely many `Γ`-orbits because each
orbit meets one of the finitely many intersections with an orbit representative of `Φ`. A finite
family of maps is handled by refining repeatedly.

Orbit finiteness of the refinement is where the finite-overlap hypothesis enters: local
finiteness of `Ψ` bounds only the cones meeting a compact subset of the open cone `C'`, and says
nothing about the cones of `Φ` in the boundary `Cstar \ C`. For `g` the identity and `Ψ = Φ` the
hypothesis holds automatically (`TauCeti.Toric.ArithmeticFan.finite_setOf_inf_comap_id`), and the
refinement is `Φ` itself (`TauCeti.Toric.ArithmeticFan.commonRefinement_self`).

## Main declarations

* `TauCeti.Toric.ArithmeticFan.commonRefinement`: the common refinement.
* `TauCeti.Toric.ArithmeticFan.exists_mem_commonRefinement_le_iff`: a cone lies in a cone of the
  common refinement exactly when it lies in a cone of `Φ` and in the preimage of a cone of `Ψ`.
  Thus each cone of the refinement lies in a cone of each input, and every system with this
  property refines the common refinement: it is the coarsest common refinement.
* `TauCeti.Toric.ArithmeticFan.support_commonRefinement`: the support is
  `Φ.support ∩ g⁻¹(Ψ.support)`, so the refinement of complete systems along a map carrying
  `Cstar` into `Cstar'` is complete (`TauCeti.Toric.ArithmeticFan.isComplete_commonRefinement`).

## References

* R. Pink, *Arithmetical compactification of mixed Shimura varieties*, Bonner Math. Schriften
  209 (1990), §§6.4–6.6 and 9.22–9.23.
* A. Ash, D. Mumford, M. Rapoport and Y.-S. Tai, *Smooth compactifications of locally symmetric
  varieties*, Chapter II.
-/

public section

namespace TauCeti.Toric.ArithmeticFan

variable {N V N' V' : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousSMul ℝ V'] [T2Space V']
  {i : N →+ V} {i' : N' →+ V'} {Γ : Subgroup (V ≃ₗ[ℝ] V)} {Γ' : Subgroup (V' ≃ₗ[ℝ] V')}
  {C Cstar : Set V} {C' Cstar' : Set V'}
  (Φ : ArithmeticFan i Γ C Cstar) (Ψ : ArithmeticFan i' Γ' C' Cstar')

variable {f : N →+ N'} (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
  (hC : Set.MapsTo g C C') (hΓ : ∀ γ ∈ Γ, ∃ γ' ∈ Γ', ∀ x, g (γ x) = γ' (g x))
  (hfin : ∀ σ ∈ Φ.cones, {ρ | ∃ τ ∈ Ψ.cones, σ ⊓ τ.comap g = ρ}.Finite)

/-- The *common refinement* of the arithmetic cone systems `Φ` and `Ψ` along an equivariant
lattice map `g` carrying the positivity cone `C` into `C'`, with finite relative overlap. Its
cones are the intersections `σ ⊓ g⁻¹(τ)` of a cone `σ` of `Φ` with the preimage of a cone `τ`
of `Ψ`; it is an arithmetic cone system for the source data `Γ`, `C` and `Cstar`. -/
def commonRefinement : ArithmeticFan i Γ C Cstar where
  lattice := Φ.lattice
  cones := {ρ | ∃ σ ∈ Φ.cones, ∃ τ ∈ Ψ.cones, σ ⊓ τ.comap g = ρ}
  isToricCone := by
    rintro _ ⟨σ, hσ, τ, hτ, rfl⟩
    exact ⟨(Φ.isToricCone hσ).rational.inf Φ.lattice.isBaseChange.equiv.injective
      ((Ψ.isToricCone hτ).rational.comap Φ.lattice Ψ.lattice hfg),
      (Φ.isToricCone hσ).salient.anti fun _ hx ↦ hx.1⟩
  coe_subset := by
    rintro _ ⟨σ, hσ, τ, -, rfl⟩ x hx
    exact Φ.coe_subset hσ hx.1
  mem_of_isFaceOf := by
    rintro _ F ⟨σ, hσ, τ, hτ, rfl⟩ hF
    have := Φ.lattice.finiteDimensional
    have := Ψ.lattice.finiteDimensional
    obtain ⟨σ', τ', hσ', hτ', rfl⟩ :=
      hF.exists_inf_comap_eq (Φ.isToricCone hσ).fg (Ψ.isToricCone hτ).fg
    exact ⟨σ', Φ.mem_of_isFaceOf hσ hσ', τ', Ψ.mem_of_isFaceOf hτ hτ', rfl⟩
  inf_isFaceOf_left := by
    rintro _ _ ⟨σ₁, hσ₁, τ₁, hτ₁, rfl⟩ ⟨σ₂, hσ₂, τ₂, hτ₂, rfl⟩
    convert (Φ.inf_isFaceOf_left hσ₁ hσ₂).inf ((Ψ.inf_isFaceOf_left hτ₁ hτ₂).comap g) using 1
    ext x
    simp only [Submodule.mem_inf, PointedCone.mem_comap]
    tauto
  map_mem := by
    rintro γ hγ _ ⟨σ, hσ, τ, hτ, rfl⟩
    obtain ⟨γ', hγ', h⟩ := hΓ γ hγ
    exact ⟨_, Φ.map_mem hγ hσ, _, Ψ.map_mem hγ' hτ,
      (PointedCone.map_inf_comap_of_comm h σ τ).symm⟩
  exists_finite_orbit_representatives := by
    obtain ⟨S, hS, hrep⟩ := Φ.exists_finite_orbit_representatives
    refine ⟨⋃ σ ∈ S ∩ Φ.cones, {ρ | ∃ τ ∈ Ψ.cones, σ ⊓ τ.comap g = ρ},
      (hS.inter_of_left _).biUnion fun σ hσ ↦ hfin σ hσ.2, ?_⟩
    rintro _ ⟨σ, hσ, τ, hτ, rfl⟩
    -- Translate `σ` back to its orbit representative `σ₀`, and `τ` along with it.
    obtain ⟨σ₀, hσ₀, γ, hγ, rfl⟩ := hrep σ hσ
    obtain ⟨γ', hγ', h⟩ := hΓ γ hγ
    have hτ' : τ.map ((γ'⁻¹ : V' ≃ₗ[ℝ] V') : V' →ₗ[ℝ] V') ∈ Ψ.cones :=
      Ψ.map_mem (inv_mem hγ') hτ
    refine ⟨_, Set.mem_biUnion ⟨hσ₀, (Φ.map_mem_iff hγ).1 hσ⟩ ⟨_, hτ', rfl⟩, γ, hγ, ?_⟩
    rw [PointedCone.map_inf_comap_of_comm h, PointedCone.map_map_linearEquiv_inv]
  finite_setOf_inter_nonempty := by
    intro K hK hKC
    have := Φ.lattice.finiteDimensional
    have hgK : IsCompact (g '' K) := hK.image g.continuous_of_finiteDimensional
    refine (((Φ.finite_setOf_inter_nonempty hK hKC).prod
      (Ψ.finite_setOf_inter_nonempty hgK (hC.mono_left hKC).image_subset)).image
        fun p ↦ p.1 ⊓ p.2.comap g).subset ?_
    rintro _ ⟨⟨σ, hσ, τ, hτ, rfl⟩, x, hx, hxK⟩
    exact ⟨(σ, τ), ⟨⟨hσ, x, hx.1, hxK⟩, hτ, g x, hx.2, x, hxK, rfl⟩, rfl⟩

variable {Φ Ψ g}

/-- A cone belongs to the common refinement exactly when it is the intersection of a cone of `Φ`
with the preimage of a cone of `Ψ`. -/
@[simp]
theorem mem_commonRefinement_cones {ρ : PointedCone ℝ V} :
    ρ ∈ (Φ.commonRefinement Ψ g hfg hC hΓ hfin).cones ↔
      ∃ σ ∈ Φ.cones, ∃ τ ∈ Ψ.cones, σ ⊓ τ.comap g = ρ :=
  Iff.rfl

/-- The intersection of a cone of `Φ` with the preimage of a cone of `Ψ` is a cone of the common
refinement. -/
theorem inf_comap_mem_commonRefinement_cones {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (hσ : σ ∈ Φ.cones) (hτ : τ ∈ Ψ.cones) :
    σ ⊓ τ.comap g ∈ (Φ.commonRefinement Ψ g hfg hC hΓ hfin).cones :=
  ⟨σ, hσ, τ, hτ, rfl⟩

/-- **The common refinement is the coarsest common refinement.** A cone lies in a cone of the
common refinement exactly when it lies in a cone of `Φ` and in the preimage of a cone of `Ψ`. In
particular every cone of the refinement lies in a cone of `Φ` and maps into a cone of `Ψ`, and
every system with that property refines the common refinement. -/
theorem exists_mem_commonRefinement_le_iff {ρ : PointedCone ℝ V} :
    (∃ ρ' ∈ (Φ.commonRefinement Ψ g hfg hC hΓ hfin).cones, ρ ≤ ρ') ↔
      (∃ σ ∈ Φ.cones, ρ ≤ σ) ∧ ∃ τ ∈ Ψ.cones, ρ ≤ τ.comap g := by
  constructor
  · rintro ⟨_, ⟨σ, hσ, τ, hτ, rfl⟩, hρ⟩
    exact ⟨⟨σ, hσ, hρ.trans inf_le_left⟩, τ, hτ, hρ.trans inf_le_right⟩
  · rintro ⟨⟨σ, hσ, hρσ⟩, τ, hτ, hρτ⟩
    exact ⟨_, inf_comap_mem_commonRefinement_cones hfg hC hΓ hfin hσ hτ, le_inf hρσ hρτ⟩

/-- The support of the common refinement is the part of the support of `Φ` that `g` maps into
the support of `Ψ`. -/
@[simp]
theorem support_commonRefinement :
    (Φ.commonRefinement Ψ g hfg hC hΓ hfin).support = Φ.support ∩ g ⁻¹' Ψ.support := by
  ext x
  simp only [mem_support, mem_commonRefinement_cones, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨σ, hσ, τ, hτ, rfl⟩, hx⟩
    exact ⟨⟨σ, hσ, hx.1⟩, τ, hτ, hx.2⟩
  · rintro ⟨⟨σ, hσ, hxσ⟩, τ, hτ, hxτ⟩
    exact ⟨_, ⟨σ, hσ, τ, hτ, rfl⟩, hxσ, hxτ⟩

/-- The common refinement of complete systems along a map carrying `Cstar` into `Cstar'` is
complete. -/
theorem isComplete_commonRefinement (hΦ : Φ.IsComplete) (hΨ : Ψ.IsComplete)
    (hCstar : Set.MapsTo g Cstar Cstar') :
    (Φ.commonRefinement Ψ g hfg hC hΓ hfin).IsComplete := by
  rw [isComplete_def, support_commonRefinement, Φ.isComplete_def.1 hΦ, Ψ.isComplete_def.1 hΨ]
  exact Set.inter_eq_left.2 hCstar

/-- Restricting the common refinement to a subgroup of finite index gives the common refinement
of the restriction, so passing to a smaller level keeps the same cones. -/
theorem restrict_commonRefinement (Γ₀ : Subgroup (V ≃ₗ[ℝ] V)) (hle : Γ₀ ≤ Γ)
    [Γ₀.IsFiniteRelIndex Γ] :
    (Φ.commonRefinement Ψ g hfg hC hΓ hfin).restrict Γ₀ hle =
      (Φ.restrict Γ₀ hle).commonRefinement Ψ g hfg hC (fun γ hγ ↦ hΓ γ (hle hγ))
        (by simpa using hfin) :=
  ArithmeticFan.ext (by ext; simp)

variable (Φ) in
/-- For a single system and the identity map, the overlap condition of the common refinement
holds automatically: each intersection `σ ⊓ τ` is a face of `σ`, and `σ` has finitely many
faces. -/
theorem finite_setOf_inf_comap_id {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) :
    {ρ | ∃ τ ∈ Φ.cones, σ ⊓ τ.comap LinearMap.id = ρ}.Finite := by
  have := PointedCone.FG.finite_face (Φ.isToricCone hσ).fg
  refine (Set.finite_range fun F : σ.Face ↦ F.toPointedCone).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  exact ⟨⟨_, by simpa using Φ.inf_isFaceOf_left hσ hτ⟩, rfl⟩

/-- The common refinement of a system with itself along the identity is the system itself. -/
@[simp]
theorem commonRefinement_self (hfg : ∀ n, LinearMap.id (i n) = i (AddMonoidHom.id N n))
    (hC : Set.MapsTo LinearMap.id C C)
    (hΓ : ∀ γ ∈ Γ, ∃ γ' ∈ Γ, ∀ x, LinearMap.id (γ x) = γ' (LinearMap.id x : V))
    (hfin : ∀ σ ∈ Φ.cones, {ρ | ∃ τ ∈ Φ.cones, σ ⊓ τ.comap LinearMap.id = ρ}.Finite) :
    Φ.commonRefinement Φ LinearMap.id hfg hC hΓ hfin = Φ := by
  ext ρ
  simp only [mem_commonRefinement_cones, PointedCone.comap_id]
  refine ⟨?_, fun hρ ↦ ⟨ρ, hρ, ρ, hρ, inf_idem ρ⟩⟩
  rintro ⟨σ, hσ, τ, hτ, rfl⟩
  exact Φ.inf_mem hσ hτ

end TauCeti.Toric.ArithmeticFan
