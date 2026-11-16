/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Pullback
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Restrict
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Hamiltonian actions of commutative Lie groups

Let a commutative Lie group `T`, such as a torus, act smoothly on a manifold `M` carrying a
two-form `σ`, and let `𝔱 = GroupLieAlgebra I T`. A **Hamiltonian torus action** with moment map
`μ : M → 𝔱*` (`TauCeti.SmoothTwoForm.HamiltonianTorusData σ μ`) is an action in which every
element of `T` pulls `σ` back to itself, and `μ` is a coadjoint-equivariant group-level moment map
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`): each component `μ_ξ` is smooth and
`σ_x(ξ_M x, v) = d(μ_ξ)_x v` for the fundamental vector field `ξ_M`.

Conjugation in a commutative group is the identity, so the adjoint and coadjoint actions are
trivial (`TauCeti.Lie.coadjointRepresentation_eq_one`), and coadjoint equivariance of `μ` says
exactly that `μ` is `T`-invariant, `μ (g • x) = μ x`. Hence an action carries Hamiltonian torus
data exactly when it preserves `σ`, `μ` is a moment map of its fundamental vector fields and `μ`
is invariant (`TauCeti.SmoothTwoForm.hamiltonianTorusData_iff`). Neither clause of the definition
follows from the other ones in general: for the translation action of `ℝ²` on itself with
`σ = dx ∧ dy`, every moment map `μ(x)(ξ) = σ(ξ, x) + c(ξ)` fails to be invariant, and the
reflection `(x, y) ↦ (x, -y)` of the zero-dimensional group `ℤ / 2` fails to preserve `σ` while
`μ = 0` satisfies the other two clauses.

Since every element of `𝔱*` is coadjoint-invariant, constant shifts of `μ` stay moment maps of
the action (`TauCeti.SmoothTwoForm.HamiltonianTorusData.add_const`), and on a preconnected
manifold they are the only other ones
(`TauCeti.SmoothTwoForm.HamiltonianTorusData.hamiltonianTorusData_iff_exists_eq_add`). For an
action preserving `σ` on a preconnected manifold, invariance of a moment map can be tested at a
single point (`TauCeti.SmoothTwoForm.IsMomentMap.hamiltonianTorusData_iff`).

Hamiltonian torus data pull back along smooth equivariant maps `f : N → M`, with form `f^* σ`
and moment map `μ ∘ f` (`TauCeti.SmoothTwoForm.HamiltonianTorusData.mpullback`); this covers
invariant open subsets and invariant submanifolds. They restrict along smooth homomorphisms
`φ : T' →* T` of commutative Lie groups, with moment map `x ↦ μ x ∘ dφ`
(`TauCeti.SmoothTwoForm.HamiltonianTorusData.comp_monoidHom`); this covers subtori and
reparametrizations of the torus. They are compatible with the diagonal action of one group on
a product (`TauCeti.SmoothTwoForm.HamiltonianTorusData.prod`) and with external products: if
`T₁` acts on `(M₁, σ₁)` with moment map `μ₁` and `T₂` on `(M₂, σ₂)` with moment map `μ₂`, then
`T₁ × T₂` acts on `M₁ × M₂` with moment map `(x₁, x₂) ↦ μ₁(x₁) ∘ pr₁ + μ₂(x₂) ∘ pr₂`
(`TauCeti.SmoothTwoForm.HamiltonianTorusData.prodMap`), where `pr₁` and `pr₂` are the
differentials at the identity of the projections of `T₁ × T₂`.

This is the structure carried by the compact Hamiltonian torus manifolds of the convexity
theorem of Atiyah and Guillemin–Sternberg and of Delzant's classification of symplectic toric
manifolds.

## Main definitions

* `TauCeti.SmoothTwoForm.HamiltonianTorusData σ μ`: the action of the commutative Lie group `T`
  on `(M, σ)` preserves `σ` and has the coadjoint-equivariant moment map `μ`.

## Main results

* `TauCeti.SmoothTwoForm.HamiltonianTorusData.apply_smul_eq`: `μ (g • x) = μ x`.
* `TauCeti.SmoothTwoForm.hamiltonianTorusData_iff`: Hamiltonian torus data are exactly an action
  preserving `σ` with a `T`-invariant moment map.
* `TauCeti.SmoothTwoForm.HamiltonianTorusData.add_const`,
  `TauCeti.SmoothTwoForm.HamiltonianTorusData.hamiltonianTorusData_iff_exists_eq_add`: the
  moment maps of a Hamiltonian torus action on a preconnected manifold are the constant shifts of
  any one of them.
* `TauCeti.SmoothTwoForm.IsMomentMap.hamiltonianTorusData_iff`: invariance of a moment map of an
  action by symplectomorphisms of a preconnected manifold can be tested at one point.
* `TauCeti.SmoothTwoForm.HamiltonianTorusData.mpullback`: pullback along a smooth equivariant
  map.
* `TauCeti.SmoothTwoForm.HamiltonianTorusData.comp_monoidHom`: restriction along a homomorphism
  of commutative Lie groups.
* `TauCeti.SmoothTwoForm.HamiltonianTorusData.prod`,
  `TauCeti.SmoothTwoForm.HamiltonianTorusData.prodMap`: diagonal and external products.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin, S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §§22, 27–28 (Hamiltonian torus actions, products and restrictions).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ μ' : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] lieGroupOne

variable (σ) in
/-- **Hamiltonian torus data.** For a smooth action of a commutative Lie group `G`, such as a
torus, on a manifold `M` with a two-form `σ`, every element of `G` pulls `σ` back to itself, and
`μ : M → 𝔤*` is a coadjoint-equivariant moment map of the action: every component `μ_ξ` is smooth
with `σ_x(ξ_M x, v) = d(μ_ξ)_x v` for the fundamental vector field `ξ_M`, and `μ` is
coadjoint-equivariant, which for commutative `G` says `μ (g • x) = μ x`
(`TauCeti.SmoothTwoForm.HamiltonianTorusData.apply_smul_eq`). -/
structure HamiltonianTorusData (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) : Prop
    extends σ.IsEquivariantMomentMap μ where
  /-- Every element of the group acts by a symplectomorphism: `g^* σ = σ`. -/
  mpullback_smul (g : G) :
    SmoothForm.mpullback (fun x : M ↦ g • x) (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ

/-- **Torus moment maps are invariant.** The coadjoint action of a commutative group is trivial,
so a moment map of Hamiltonian torus data is constant along orbits. -/
theorem HamiltonianTorusData.apply_smul_eq (h : σ.HamiltonianTorusData μ) (g : G) (x : M) :
    μ (g • x) = μ x := by
  rw [h.apply_smul, Lie.coadjointRepresentation_eq_one, one_apply_eq_self]

/-- **Characterization of Hamiltonian torus data.** An action of a commutative Lie group carries
Hamiltonian torus data with moment map `μ` exactly when it preserves `σ`, `μ` is a moment map of
its fundamental vector fields, and `μ` is invariant under the action. -/
theorem hamiltonianTorusData_iff :
    σ.HamiltonianTorusData μ ↔
      (∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
        (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) ∧
      σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ ∧
      ∀ (g : G) (x : M), μ (g • x) = μ x := by
  refine ⟨fun h ↦ ⟨h.mpullback_smul, h.toIsMomentMap, h.apply_smul_eq⟩,
    fun ⟨hσ, hμ, hinv⟩ ↦ ⟨⟨hμ, fun g x ↦ ?_⟩, hσ⟩⟩
  rw [hinv, Lie.coadjointRepresentation_eq_one, one_apply_eq_self]

/-- **Invariance can be tested at one point.** For an action of a commutative Lie group by
symplectomorphisms of a preconnected manifold, a moment map of the action gives Hamiltonian
torus data as soon as `μ (g • x₀) = μ x₀` for every `g` at a single point `x₀`, for instance at a
fixed point of the action. -/
theorem IsMomentMap.hamiltonianTorusData_iff [PreconnectedSpace M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hσ : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) (x₀ : M) :
    σ.HamiltonianTorusData μ ↔ ∀ g : G, μ (g • x₀) = μ x₀ := by
  refine ⟨fun h' g ↦ h'.apply_smul_eq g x₀, fun h₀ ↦ ⟨(h.isEquivariantMomentMap_iff hσ x₀).2
    fun g ↦ ?_, hσ⟩⟩
  rw [h₀, Lie.coadjointRepresentation_eq_one, one_apply_eq_self]

namespace HamiltonianTorusData

/-- **Constant shifts.** Shifting the moment map of Hamiltonian torus data by any constant
`ν ∈ 𝔤*` gives Hamiltonian torus data, since every element of `𝔤*` is coadjoint-invariant for a
commutative group. -/
theorem add_const (h : σ.HamiltonianTorusData μ) (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    σ.HamiltonianTorusData fun x ↦ μ x + ν :=
  hamiltonianTorusData_iff.2 ⟨h.mpullback_smul, h.toIsMomentMap.add_const ν,
    fun g x ↦ by rw [h.apply_smul_eq]⟩

/-- The negative of a moment map of Hamiltonian torus data for `σ` is a moment map of Hamiltonian
torus data for the opposite form `-σ`. -/
theorem neg (h : σ.HamiltonianTorusData μ) : (-σ).HamiltonianTorusData fun x ↦ -μ x where
  toIsEquivariantMomentMap := h.toIsEquivariantMomentMap.neg
  mpullback_smul g := by rw [map_neg, h.mpullback_smul]

/-- **Uniqueness of torus moment maps.** On a preconnected manifold, the moment maps of a
Hamiltonian torus action are exactly the shifts `x ↦ μ x + ν` of any one of them `μ` by constants
`ν ∈ 𝔤*`. -/
theorem hamiltonianTorusData_iff_exists_eq_add [PreconnectedSpace M]
    (h : σ.HamiltonianTorusData μ) :
    σ.HamiltonianTorusData μ' ↔
      ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G), μ' = fun x ↦ μ x + ν := by
  refine ⟨fun h' ↦ ?_, fun ⟨ν, hν⟩ ↦ hν ▸ h.add_const ν⟩
  obtain ⟨ν, -, hν⟩ :=
    h.toIsEquivariantMomentMap.isEquivariantMomentMap_iff_exists_eq_add.1
      h'.toIsEquivariantMomentMap
  exact ⟨ν, hν⟩

/-- **Pullback along an equivariant map.** If `f : N → M` is a smooth `G`-equivariant map and
`μ` is the moment map of Hamiltonian torus data for `σ`, then `μ ∘ f` is the moment map of
Hamiltonian torus data for the pullback `f^* σ`. -/
theorem mpullback {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [CompleteSpace EN]
    [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N]
    [ChartedSpace HN N] [IsManifold IN ∞ N] [MulAction G N] [ContMDiffSMul I IN ∞ G N]
    (h : σ.HamiltonianTorusData μ) {f : N → M} (hf : ContMDiff IN I' ∞ f)
    (hfg : ∀ (g : G) (y : N), f (g • y) = g • f y) :
    HamiltonianTorusData (SmoothForm.mpullback f hf σ) (μ ∘ f) where
  toIsEquivariantMomentMap := h.toIsEquivariantMomentMap.mpullback hf hfg
  mpullback_smul g := by
    -- Both sides pull `σ` back along `f`, since `f ∘ (g • ·) = (g • ·) ∘ f`.
    conv_rhs => rw [← h.mpullback_smul g]
    rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
    have hcomp : f ∘ (fun y : N ↦ g • y) = (fun x : M ↦ g • x) ∘ f := funext (hfg g)
    simp only [hcomp]

section Restrict

variable {F HK : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [CommGroup K]
  [LieGroup J (minSmoothness ℝ 3) K] [MulAction K M] [ContMDiffSMul J I' ∞ K M]

/-- **Restriction along a homomorphism.** If a commutative Lie group `K` acts through a
homomorphism `φ : K →* G` that is differentiable at the identity, `k • x = φ k • x`, then
Hamiltonian torus data for `G` with moment map `μ` restrict to Hamiltonian torus data for `K`
with moment map `x ↦ μ x ∘ dφ`, where `dφ` is the differential of `φ` at the identity. -/
theorem comp_monoidHom (h : σ.HamiltonianTorusData μ) (φ : K →* G)
    (hφ : MDifferentiableAt J I φ 1) (hsmul : ∀ (k : K) (x : M), k • x = φ k • x) :
    σ.HamiltonianTorusData fun x ↦ (μ x).comp (φ.groupLieAlgebraMap J I).toLinearMap where
  toIsEquivariantMomentMap := h.toIsEquivariantMomentMap.comp_monoidHom φ hφ hsmul
  mpullback_smul k := by simpa only [hsmul] using h.mpullback_smul (φ k)

end Restrict

section Prod

variable {F H₂ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H₂] {J : ModelWithCorners ℝ F H₂}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold J ∞ N]

/-- **Diagonal products.** If a commutative Lie group acts on `(M, σ)` and on `(N, τ)` with
Hamiltonian torus data `μ` and `ν`, its diagonal action on `M × N` carries Hamiltonian torus data
for the product form, with moment map `(x, y) ↦ μ x + ν y`. -/
theorem prod [MulAction G N] [ContMDiffSMul I J ∞ G N] {τ : SmoothTwoForm J N}
    {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)} (h : σ.HamiltonianTorusData μ)
    (h' : τ.HamiltonianTorusData ν) :
    (σ.prod τ).HamiltonianTorusData fun p ↦ μ p.1 + ν p.2 where
  toIsEquivariantMomentMap := h.toIsEquivariantMomentMap.prod h'.toIsEquivariantMomentMap
  mpullback_smul g := by
    have hg := mpullback_prodMap_prod (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := J) g) σ τ
    rw [h.mpullback_smul, h'.mpullback_smul] at hg
    -- On `M × N`, `g` acts by definition as the product map of its actions on the factors.
    exact hg

variable {E₂ HG₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
  [TopologicalSpace HG₂] {I₂ : ModelWithCorners ℝ E₂ HG₂}
  {G₂ : Type*} [TopologicalSpace G₂] [ChartedSpace HG₂ G₂] [CommGroup G₂]
  [LieGroup I₂ (minSmoothness ℝ 3) G₂] [MulAction G₂ N] [ContMDiffSMul I₂ J ∞ G₂ N]

/-- **External products.** If `G` acts on `(M, σ)` with Hamiltonian torus data `μ` and `G₂` acts on
`(N, τ)` with Hamiltonian torus data `ν`, then the componentwise action of `G × G₂` on `M × N`,
`(g, g₂) • (x, y) = (g • x, g₂ • y)`, carries Hamiltonian torus data for the product form, with
moment map `(x, y) ↦ μ x ∘ pr₁ + ν y ∘ pr₂`. Here `pr₁` and `pr₂` are the differentials at the
identity of the projections of `G × G₂`. -/
theorem prodMap [inst : MulAction (G × G₂) (M × N)]
    [ContMDiffSMul (I.prod I₂) (I'.prod J) ∞ (G × G₂) (M × N)]
    (hsmul : ∀ (g : G × G₂) (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) {τ : SmoothTwoForm J N}
    {ν : N → Module.Dual ℝ (GroupLieAlgebra I₂ G₂)} (h : σ.HamiltonianTorusData μ)
    (h' : τ.HamiltonianTorusData ν) :
    (σ.prod τ).HamiltonianTorusData fun p ↦
      (μ p.1).comp ((MonoidHom.fst G G₂).groupLieAlgebraMap (I.prod I₂) I).toLinearMap +
        (ν p.2).comp ((MonoidHom.snd G G₂).groupLieAlgebraMap (I.prod I₂) I₂).toLinearMap := by
  -- Let `G × G₂` act on each factor through the corresponding projection; the given action is
  -- then the diagonal action of `G × G₂` on `M × N`.
  let _ : MulAction (G × G₂) M := MulAction.compHom M (MonoidHom.fst G G₂)
  let _ : MulAction (G × G₂) N := MulAction.compHom N (MonoidHom.snd G G₂)
  have _ : ContMDiffSMul (I.prod I₂) I' ∞ (G × G₂) M :=
    MulAction.contMDiffSMul_compHom (I := I) (f := MonoidHom.fst G G₂) contMDiff_fst
  have _ : ContMDiffSMul (I.prod I₂) J ∞ (G × G₂) N :=
    MulAction.contMDiffSMul_compHom (I := I₂) (f := MonoidHom.snd G G₂) contMDiff_snd
  -- By definition of `MulAction.compHom`, `g • x = g.1 • x` on `M` and `g • y = g.2 • y` on `N`.
  obtain rfl : inst = Prod.mulAction := MulAction.ext (funext₂ hsmul)
  exact (h.comp_monoidHom (MonoidHom.fst G G₂) mdifferentiableAt_fst fun _ _ ↦ rfl).prod
    (h'.comp_monoidHom (MonoidHom.snd G G₂) mdifferentiableAt_snd fun _ _ ↦ rfl)

end Prod

end HamiltonianTorusData

end TauCeti.SmoothTwoForm
