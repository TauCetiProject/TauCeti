/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.RepresentationTheory.Pi.External
public import TauCeti.Topology.ImplicitAtlas.Examples
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Linear

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

* An atlas whose stabilizers at regular zeros are trivial is locally orientable
  (`TauCeti.ImplicitAtlas.isLocallyOrientable_of_forall_eq_one`); in particular one with trivial
  isotropy groups (`TauCeti.ImplicitAtlas.isLocallyOrientable_of_subsingleton`), such as the
  manifold atlas (`TauCeti.ImplicitAtlas.isLocallyOrientable_ofChartedSpace`) and Pardon's atlas
  `s(x) = xᵐ` on a point (`TauCeti.ImplicitAtlas.isLocallyOrientable_powAtlas`).
* In the atlases on a point with thickening `X_α = ℝ` on which `ℤˣ = {±1}` acts by `x ↦ ±x`,
  `u ∈ ℤˣ` acts on `o_0 = H₁(ℝ, ℝ ∖ {0}; ℤ)` by `u`
  (`TauCeti.ImplicitAtlas.localHomologyMap_pointAct_unitsIntAction`). So the reflection atlas
  `s(x) = xᵐ`, `m` even, with `ℤˣ` acting trivially on `E_α = ℝ`, is not locally orientable
  (`TauCeti.ImplicitAtlas.not_isLocallyOrientable_reflectionAtlas`): at `0` the reflection acts on
  `o_0 ⊗ o_(E_α)^∨` by `(-1)(+1) = -1`. The odd reflection atlas `s(x) = xᵐ`, `m` odd, with `ℤˣ`
  reflecting `E_α` as well, is locally orientable
  (`TauCeti.ImplicitAtlas.isLocallyOrientable_oddReflectionAtlas`): the reflection acts by
  `(-1)(-1) = +1`, although it acts nontrivially on each factor.

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

section ChartedSpace

variable {A : Type*} [IsEmpty A] [DecidableEq A] (Γ : A → Type*) [∀ α, Group (Γ α)]
  [∀ α, Finite (Γ α)] (E : A → Type*) [∀ α, NormedAddCommGroup (E α)]
  [∀ α, NormedSpace ℝ (E α)] [∀ α, FiniteDimensional ℝ (E α)]
  (ρ : ∀ α, Representation ℝ (Γ α) (E α)) (n : ℕ) (X : Type w) [TopologicalSpace X]
  [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

/-- The manifold atlas of a topological manifold is locally orientable, although the manifold
need not be orientable: its index set is empty, so every isotropy group is trivial. -/
theorem isLocallyOrientable_ofChartedSpace : (ofChartedSpace Γ E ρ n X).IsLocallyOrientable :=
  have : ∀ α, Subsingleton (Γ α) := fun α ↦ isEmptyElim α
  isLocallyOrientable_of_subsingleton _

end ChartedSpace

/-! ### Atlases on a point with a reflection -/

section Reflection

/-- In a single-chart atlas on the point `0` with thickening `X_α = ℝ` on which `ℤˣ = {±1}` acts
by `x ↦ ±x`, the element `u` of `Γ_α = ℤˣ` acts on the local orientation line
`H_k(ℝ, ℝ ∖ {0}; ℤ)` of `X_α` at `0` by `u`, as the linear map `x ↦ u x` of determinant `u` does
(`TauCeti.singularHomologyMap_continuousLinearMap_compl_zero`). -/
theorem localHomologyMap_pointAct_unitsIntAction (hσ : ∀ u, unitsIntAction u 0 = 0)
    (g : (α : ({()} : Finset Unit)) → ℤˣ) {x : PointThickening ℝ 0 {()}} (hx : (x : ℝ) = 0)
    (h : ⇑(pointAct unitsIntAction hσ {()} g :
      C(PointThickening ℝ 0 {()}, PointThickening ℝ 0 {()})) ⁻¹' {x} ⊆ {x}) (k : ℕ) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (pointAct unitsIntAction hσ {()} g : C(PointThickening ℝ 0 {()}, PointThickening ℝ 0 {()}))
        h k = ((g ⟨(), Finset.mem_singleton_self ()⟩ : ℤˣ) : ℤ) • 𝟙 _ := by
  set u := g ⟨(), Finset.mem_singleton_self ()⟩
  let φ := pointThickeningHomeomorph (y₀ := (0 : ℝ)) (Finset.singleton_nonempty ())
  let φc : C(PointThickening ℝ 0 {()}, ℝ) := φ
  let ψc : C(ℝ, PointThickening ℝ 0 {()}) := φ.symm
  let f : ℝ →L[ℝ] ℝ := ((u : ℤ) : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hu : ((u : ℤ) : ℝ) ≠ 0 := by simp
  -- The action of `u` is the multiplication `f` by `u`, read through `X_α ≃ₜ ℝ`.
  have hact : (pointAct unitsIntAction hσ {()} g :
      C(PointThickening ℝ 0 {()}, PointThickening ℝ 0 {()})) = ψc.comp ((f : C(ℝ, ℝ)).comp φc) := by
    ext y
    simp [φc, ψc, φ, f, u, pointComponent_of_mem (Finset.mem_singleton_self ())]
  have hφ : ⇑φc ⁻¹' {0} ⊆ {x} := fun y hy ↦
    Subtype.ext ((show (y : ℝ) = 0 by simpa [φc, φ] using hy).trans hx.symm)
  have hf : ⇑(f : C(ℝ, ℝ)) ⁻¹' {0} ⊆ {0} := fun y hy ↦ by
    simpa [f, hu] using hy
  have hψ : ⇑ψc ⁻¹' {x} ⊆ {0} := fun y hy ↦ by
    simpa [ψc, φ, hx] using congrArg Subtype.val hy
  have hmid : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f : C(ℝ, ℝ)) hf k =
      ((u : ℤ) : ℤ) • 𝟙 _ := by
    have hdet : f.det = (u : ℤ) := by
      simp [f, ContinuousLinearMap.det]
    rw [localHomologyMap_def, singularHomologyMap_continuousLinearMap_compl_zero, hdet]
    rcases Int.units_eq_one_or u with hu' | hu' <;> simp [hu']
  have hid : ψc.comp φc = ContinuousMap.id (PointThickening ℝ 0 {()}) := by
    ext
    simp [φc, ψc, φ]
  refine (localHomologyMap_congr _ hact h k).trans ?_
  calc _ = localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) φc hφ k ≫
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (f : C(ℝ, ℝ)) hf k ≫
          localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ψc hψ k := by
        rw [localHomologyMap_comp, localHomologyMap_comp]
        exact localHomologyMap_congr _ (ContinuousMap.comp_assoc _ _ _).symm _ k
    _ = ((u : ℤ) : ℤ) • 𝟙 _ := by
        rw [hmid, Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul,
          localHomologyMap_comp]
        rw [localHomologyMap_eq_id _ hid _ k]

/-- At a point of `X_α = ℝ`, the integral local orientation line `H₁(ℝ, ℝ ∖ {x}; ℤ) ≅ ℤ` is not
`2`-torsion, so `-1` does not act on it as the identity. -/
private theorem neg_one_zsmul_id_ne_id (x : PointThickening ℝ 0 {()}) :
    (-1 : ℤ) • 𝟙 (localHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) {x} 1) ≠ 𝟙 _ := by
  intro h
  let φ := pointThickeningHomeomorph (y₀ := (0 : ℝ)) (Finset.singleton_nonempty ())
  let e := singularHomologyComplSingletonIsoOfFinrankEq (ModuleCat.of ℤ (ULift.{0} ℤ))
    φ.toOpenPartialHomeomorph (x := x) (by simp) (n := 0) (by simp)
  have h' := congrArg (fun t ↦ e.inv ≫ t ≫ e.hom) h
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
    Iso.inv_hom_id] at h'
  have h'' := congrArg (fun t ↦ t.hom (ULift.up (1 : ℤ))) h'
  simp only [ModuleCat.hom_zsmul, ModuleCat.hom_id] at h''
  have := congrArg ULift.down h''
  simp at this

/-- **The reflection atlas is not locally orientable.** At the regular zero `0` of `X_α = ℝ` the
reflection `x ↦ -x` acts on the local orientation line by `-1`, and on that of `E_α = ℝ`, where it
acts trivially, by `+1`. -/
theorem not_isLocallyOrientable_reflectionAtlas {m : ℕ} (hm : Even m) (hm₀ : m ≠ 0) :
    ¬ (reflectionAtlas hm hm₀).IsLocallyOrientable := by
  intro h
  let x : PointThickening ℝ 0 {()} := ⟨0, fun _ ↦ rfl⟩
  have := h.localHomologyMap_eq (I := {()}) (x := x) (by simp [regLocus_reflectionAtlas])
    (mem_kuranishiZeroSet.2 fun _ _ ↦ by simp [x, hm₀]) (g := fun _ ↦ -1)
    (Subtype.ext (by simp [x, pointComponent_of_mem])) (n := 1) (by simp)
  rw [localHomologyMap_pointAct_unitsIntAction _ _ rfl, Representation.det_externalPi] at this
  have htriv (u : ℤˣ) : Representation.trivial ℝ ℤˣ ℝ u = 1 :=
    LinearMap.ext (Representation.trivial_apply ℝ u)
  simp only [htriv, map_one, Finset.prod_const_one, sign_one, SignType.coe_one, one_smul] at this
  exact neg_one_zsmul_id_ne_id x this

/-- **The odd reflection atlas is locally orientable.** At the regular zero `0` of `X_α = ℝ` the
reflection `x ↦ -x` acts by `-1` both on the local orientation line and on the orientation line of
`E_α = ℝ`, so it acts trivially on their tensor product. -/
theorem isLocallyOrientable_oddReflectionAtlas {m : ℕ} (hm : Odd m) :
    (oddReflectionAtlas hm).IsLocallyOrientable := by
  refine isLocallyOrientable_iff.2 fun I x hx hx₀ g hg n _ ↦ ?_
  rw [regLocus_oddReflectionAtlas] at hx
  rw [kuranishi_oddReflectionAtlas] at hx₀
  obtain ⟨⟨⟩, hI⟩ : I.Nonempty := hx
  obtain rfl : I = {()} := Finset.eq_singleton_iff_unique_mem.2 ⟨hI, fun _ _ ↦ rfl⟩
  rw [localHomologyMap_pointAct_unitsIntAction _ _ (coe_eq_of_mem_kuranishiZeroSet_pointKuranishi
    (fun _ ↦ pow_eq_zero_iff hm.pos.ne') (Finset.notMem_empty _) hx₀),
    Representation.det_externalPi]
  congr 1
  rcases Int.units_eq_one_or (g ⟨(), Finset.mem_singleton_self ()⟩) with hu | hu <;>
    simp [hu]

end Reflection

/-- **Pardon's atlas `s(x) = xᵐ` on a point is locally orientable**: its isotropy groups are
trivial. -/
theorem isLocallyOrientable_powAtlas {m : ℕ} (hm : m ≠ 0) : (powAtlas hm).IsLocallyOrientable :=
  isLocallyOrientable_of_subsingleton _

end TauCeti.ImplicitAtlas
