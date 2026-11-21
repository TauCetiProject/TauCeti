/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Morphisms of Ehresmann connections

Let `D` be an Ehresmann connection on `π : P → B` and `D'` one on `ρ : Q → C`. A pair of
differentiable maps `Φ : P → Q` and `φ : B → C` is a **morphism of Ehresmann connections**
(`TauCeti.IsEhresmannConnectionHom`) when it covers the projections, `ρ ∘ Φ = φ ∘ π`, and the
derivative of `Φ` carries horizontal vectors to horizontal vectors. Writing `h` and `k` for the
horizontal lifts of the two connections, the second condition is equivalent to the identity
`dΦ ∘ h = k ∘ dφ` of maps `T_(π x) B → T_(Φ x) Q`
(`TauCeti.IsEhresmannConnectionHom.mfderiv_horizontalLift` and
`TauCeti.IsEhresmannConnectionHom.of_mfderiv_horizontalLift`). As `Φ` covers `φ`, its derivative
also carries vertical vectors to vertical vectors, so it intertwines the horizontal and vertical
projections of the two connections.

The identity is a morphism and morphisms compose, so Ehresmann connections and their morphisms
form a category. If `Φ` has a differentiable two-sided inverse `Φ'` and `φ` a differentiable left
inverse `φ'`, then `(Φ', φ')` is a morphism in the opposite direction. In particular, if `Φ` and
`φ` are diffeomorphisms then the pair of inverse diffeomorphisms is again a morphism, so `(Φ, φ)`
is an isomorphism of connections. Such isomorphisms compare connections related by changes of
coordinates or by symmetries.

The base field `𝕜` is arbitrary. Over `ℂ` with complex manifolds the differentiable maps are the
holomorphic ones, so the same predicate describes morphisms of holomorphic connections.

## Main definitions

* `TauCeti.IsEhresmannConnectionHom I J I' J' π D ρ D' Φ φ`: `(Φ, φ)` is a morphism from the
  connection `D` on `π` to the connection `D'` on `ρ`.

## Main results

* `TauCeti.IsEhresmannConnectionHom.mfderiv_horizontalLift`: a morphism intertwines the horizontal
  lifts, `dΦ ∘ h = k ∘ dφ`.
* `TauCeti.IsEhresmannConnectionHom.of_mfderiv_horizontalLift`: conversely, a covering pair of
  differentiable maps intertwining the horizontal lifts is a morphism.
* `TauCeti.IsEhresmannConnectionHom.mfderiv_horizontalProjection` and
  `TauCeti.IsEhresmannConnectionHom.mfderiv_verticalProjection`: a morphism intertwines the
  horizontal and vertical projections.
* `TauCeti.IsEhresmannConnectionHom.id` and `TauCeti.IsEhresmannConnectionHom.comp`: identities
  and composites of morphisms are morphisms.
* `TauCeti.IsEhresmannConnectionHom.inverse` and `TauCeti.IsEhresmannConnectionHom.symm`: the
  inverse of an invertible morphism, in particular of a pair of diffeomorphisms, is a morphism.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.3 (connections on fibred manifolds) and §9.6 (connections related by fibred
  morphisms).
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {C : Type*} [TopologicalSpace C] [ChartedSpace G' C]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {R : Type*} [TopologicalSpace R] [ChartedSpace H'' R]
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {G'' : Type*} [TopologicalSpace G''] {J'' : ModelWithCorners 𝕜 F'' G''}
  {A : Type*} [TopologicalSpace A] [ChartedSpace G'' A]
  {π : P → B} {D : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  {ρ : Q → C} {D' : Π y : Q, Submodule 𝕜 (TangentSpace I' y)}
  {σ : R → A} {D'' : Π z : R, Submodule 𝕜 (TangentSpace I'' z)}
  {Φ : P → Q} {φ : B → C}

variable (I J I' J') in
/-- A pair of maps `Φ : P → Q` and `φ : B → C` is a **morphism of Ehresmann connections** from the
horizontal distribution `D` of `π : P → B` to the horizontal distribution `D'` of `ρ : Q → C` when
both maps are differentiable, `Φ` covers `φ` (`ρ ∘ Φ = φ ∘ π`), and the derivative of `Φ` maps
every horizontal space `D x` into the horizontal space `D' (Φ x)`. -/
@[mk_iff]
structure IsEhresmannConnectionHom (π : P → B) (D : Π x : P, Submodule 𝕜 (TangentSpace I x))
    (ρ : Q → C) (D' : Π y : Q, Submodule 𝕜 (TangentSpace I' y)) (Φ : P → Q) (φ : B → C) :
    Prop where
  /-- The map of total spaces is differentiable. -/
  mdifferentiable : MDifferentiable I I' Φ
  /-- The map of bases is differentiable. -/
  mdifferentiable_base : MDifferentiable J J' φ
  /-- The map of total spaces covers the map of bases. -/
  comp_eq : ρ ∘ Φ = φ ∘ π
  /-- The derivative of the map of total spaces preserves horizontality. -/
  mfderiv_mem (x : P) {v : TangentSpace I x} (hv : v ∈ D x) : mfderiv I I' Φ x v ∈ D' (Φ x)

/-- If `g ∘ f = id` for differentiable maps `f` and `g`, then `dg_(f x) ∘ df_x = id`. -/
private theorem mfderiv_apply_mfderiv_apply_of_leftInverse {f : P → Q} {g : Q → P} {x : P}
    (hg : MDifferentiableAt I' I g (f x)) (hf : MDifferentiableAt I I' f x)
    (hl : LeftInverse g f) (u : TangentSpace I x) :
    mfderiv I' I g (f x) (mfderiv I I' f x u) = u := by
  rw [← mfderiv_comp_apply x hg hf, hl.comp_eq_id, mfderiv_id, ContinuousLinearMap.id_apply]

namespace IsEhresmannConnectionHom

section Lifts

variable (h : IsEhresmannConnectionHom I J I' J' π D ρ D' Φ φ)
include h

/-- A morphism intertwines the derivatives of the projections: `dρ ∘ dΦ = dφ ∘ dπ`. -/
theorem mfderiv_apply_mfderiv_apply {x : P} (hπ : MDifferentiableAt I J π x)
    (hρ : MDifferentiableAt I' J' ρ (Φ x)) (v : TangentSpace I x) :
    mfderiv I' J' ρ (Φ x) (mfderiv I I' Φ x v) = mfderiv J J' φ (π x) (mfderiv I J π x v) := by
  rw [← mfderiv_comp_apply x hρ (h.mdifferentiable x),
    ← mfderiv_comp_apply x (h.mdifferentiable_base _) hπ, h.comp_eq]

/-- The derivative of a morphism carries vertical vectors to vertical vectors. -/
theorem mfderiv_mem_ker {x : P} (hπ : MDifferentiableAt I J π x)
    (hρ : MDifferentiableAt I' J' ρ (Φ x)) {v : TangentSpace I x}
    (hv : v ∈ (mfderiv I J π x).ker) : mfderiv I I' Φ x v ∈ (mfderiv I' J' ρ (Φ x)).ker :=
  LinearMap.mem_ker.2 <| (h.mfderiv_apply_mfderiv_apply hπ hρ v).trans <|
    (congrArg (mfderiv J J' φ (π x)) (LinearMap.mem_ker.1 hv)).trans (map_zero _)

variable [IsManifold I 1 P] [IsManifold I' 1 Q] {n n' : ℕ∞ω}
  (hD : IsEhresmannConnection I J n π D) (hD' : IsEhresmannConnection I' J' n' ρ D')
include hD hD'

/-- **Morphisms intertwine horizontal lifts.** If `(Φ, φ)` is a morphism of Ehresmann
connections with horizontal lifts `h` and `k`, then `dΦ ∘ h = k ∘ dφ`. -/
theorem mfderiv_horizontalLift (x : P) (v : TangentSpace J (π x)) :
    mfderiv I I' Φ x (hD.horizontalLift x v) = hD'.horizontalLift (Φ x) (mfderiv J J' φ (π x) v) :=
  congrArg Subtype.val <| hD'.eq_horizontalLift_iff (w := ⟨_, h.mfderiv_mem x (Subtype.prop _)⟩)
    |>.2 <| (h.mfderiv_apply_mfderiv_apply (hD.mdifferentiable x) (hD'.mdifferentiable _) _).trans
      <| by rw [hD.mfderiv_horizontalLift]

/-- **Morphisms intertwine horizontal projections.** -/
theorem mfderiv_horizontalProjection (x : P) (v : TangentSpace I x) :
    mfderiv I I' Φ x (hD.horizontalProjection x v) =
      hD'.horizontalProjection (Φ x) (mfderiv I I' Φ x v) := by
  rw [hD.horizontalProjection_apply, h.mfderiv_horizontalLift hD hD',
    hD'.horizontalProjection_apply,
    h.mfderiv_apply_mfderiv_apply (hD.mdifferentiable x) (hD'.mdifferentiable _)]

/-- **Morphisms intertwine vertical projections.** -/
theorem mfderiv_verticalProjection (x : P) (v : TangentSpace I x) :
    mfderiv I I' Φ x (hD.verticalProjection x v) =
      hD'.verticalProjection (Φ x) (mfderiv I I' Φ x v) := by
  rw [hD.verticalProjection_apply, map_sub, h.mfderiv_horizontalLift hD hD',
    hD'.verticalProjection_apply,
    h.mfderiv_apply_mfderiv_apply (hD.mdifferentiable x) (hD'.mdifferentiable _)]

omit h

/-- A covering pair of differentiable maps which intertwines the horizontal lifts,
`dΦ ∘ h = k ∘ dφ`, is a morphism of Ehresmann connections. -/
theorem of_mfderiv_horizontalLift (hΦ : MDifferentiable I I' Φ) (hφ : MDifferentiable J J' φ)
    (hcomm : ρ ∘ Φ = φ ∘ π)
    (hlift : ∀ x (v : TangentSpace J (π x)), mfderiv I I' Φ x (hD.horizontalLift x v) =
      hD'.horizontalLift (Φ x) (mfderiv J J' φ (π x) v)) :
    IsEhresmannConnectionHom I J I' J' π D ρ D' Φ φ where
  mdifferentiable := hΦ
  mdifferentiable_base := hφ
  comp_eq := hcomm
  mfderiv_mem x v hv := by
    have hv' : (hD.horizontalLift x (mfderiv I J π x v) : TangentSpace I x) = v :=
      congrArg Subtype.val (hD.horizontalLift_mfderiv x ⟨v, hv⟩)
    rw [← hv', hlift]
    exact Subtype.prop _

/-- A covering pair of differentiable maps is a morphism of Ehresmann connections if and only if
it intertwines the horizontal lifts, `dΦ ∘ h = k ∘ dφ`. -/
theorem _root_.TauCeti.isEhresmannConnectionHom_iff_mfderiv_horizontalLift
    (hΦ : MDifferentiable I I' Φ) (hφ : MDifferentiable J J' φ) (hcomm : ρ ∘ Φ = φ ∘ π) :
    IsEhresmannConnectionHom I J I' J' π D ρ D' Φ φ ↔
      ∀ x (v : TangentSpace J (π x)), mfderiv I I' Φ x (hD.horizontalLift x v) =
        hD'.horizontalLift (Φ x) (mfderiv J J' φ (π x) v) :=
  ⟨fun h ↦ h.mfderiv_horizontalLift hD hD', of_mfderiv_horizontalLift hD hD' hΦ hφ hcomm⟩

end Lifts

/-! ### Identities, composites and inverses -/

/-- The identity is a morphism of Ehresmann connections. -/
theorem id : IsEhresmannConnectionHom I J I J π D π D id id where
  mdifferentiable := mdifferentiable_id
  mdifferentiable_base := mdifferentiable_id
  comp_eq := rfl
  mfderiv_mem x v hv := by rwa [mfderiv_id]

/-- The composite of morphisms of Ehresmann connections is a morphism. -/
theorem comp {Ψ : Q → R} {ψ : C → A} (h₂ : IsEhresmannConnectionHom I' J' I'' J'' ρ D' σ D'' Ψ ψ)
    (h₁ : IsEhresmannConnectionHom I J I' J' π D ρ D' Φ φ) :
    IsEhresmannConnectionHom I J I'' J'' π D σ D'' (Ψ ∘ Φ) (ψ ∘ φ) where
  mdifferentiable := h₂.mdifferentiable.comp h₁.mdifferentiable
  mdifferentiable_base := h₂.mdifferentiable_base.comp h₁.mdifferentiable_base
  comp_eq := by rw [← Function.comp_assoc, h₂.comp_eq, Function.comp_assoc, h₁.comp_eq,
    Function.comp_assoc]
  mfderiv_mem x v hv := by
    rw [mfderiv_comp_apply x (h₂.mdifferentiable _) (h₁.mdifferentiable x)]
    exact h₂.mfderiv_mem _ (h₁.mfderiv_mem x hv)

/-- **Inverses of morphisms.** If `(Φ, φ)` is a morphism of Ehresmann connections and `Φ'`, `φ'`
are differentiable maps, `Φ'` a two-sided inverse of `Φ` and `φ'` a left inverse of `φ`, then
`(Φ', φ')` is a morphism in the opposite direction. -/
theorem inverse [IsManifold I 1 P] [IsManifold I' 1 Q] {n n' : ℕ∞ω}
    (h : IsEhresmannConnectionHom I J I' J' π D ρ D' Φ φ)
    (hD : IsEhresmannConnection I J n π D) (hD' : IsEhresmannConnection I' J' n' ρ D')
    {Φ' : Q → P} {φ' : C → B} (hΦ' : MDifferentiable I' I Φ') (hφ' : MDifferentiable J' J φ')
    (hl : LeftInverse Φ' Φ) (hr : RightInverse Φ' Φ) (hφl : LeftInverse φ' φ) :
    IsEhresmannConnectionHom I' J' I J ρ D' π D Φ' φ' where
  mdifferentiable := hΦ'
  mdifferentiable_base := hφ'
  comp_eq := by
    ext y
    simp only [Function.comp_apply]
    conv_rhs => rw [← hr y]
    rw [← Function.comp_apply (f := ρ), h.comp_eq, Function.comp_apply, hφl]
  mfderiv_mem y w hw := by
    -- With `x = Φ' y`, the derivative `dΦ_x` is injective and maps both `dΦ'_y w` and the
    -- horizontal lift of `dπ (dΦ'_y w)` to `w`.
    have hw₀ : w ∈ D' (Φ (Φ' y)) := (hr y).symm ▸ hw
    have hinj : Injective (mfderiv I I' Φ (Φ' y)) :=
      LeftInverse.injective (g := mfderiv I' I Φ' (Φ (Φ' y))) fun u ↦
        mfderiv_apply_mfderiv_apply_of_leftInverse (hΦ' _) (h.mdifferentiable (Φ' y)) hl u
    have hw' : mfderiv I I' Φ (Φ' y) (mfderiv I' I Φ' y w) = w :=
      mfderiv_apply_mfderiv_apply_of_leftInverse (h.mdifferentiable _) (hΦ' y) hr w
    -- `w` is horizontal, so it is the horizontal lift of `dρ w = dφ (dπ (dΦ'_y w))`.
    have hρw : mfderiv I' J' ρ (Φ (Φ' y)) w =
        mfderiv J J' φ (π (Φ' y)) (mfderiv I J π (Φ' y) (mfderiv I' I Φ' y w)) := by
      rw [← h.mfderiv_apply_mfderiv_apply (hD.mdifferentiable _) (hD'.mdifferentiable _), hw']
    have hz : mfderiv I' I Φ' y w =
        hD.horizontalLift (Φ' y) (mfderiv I J π (Φ' y) (mfderiv I' I Φ' y w)) := by
      apply hinj
      rw [hw', h.mfderiv_horizontalLift hD hD']
      exact congrArg Subtype.val ((hD'.eq_horizontalLift_iff
        (x := Φ (Φ' y)) (w := ⟨w, hw₀⟩)).2 hρw)
    rw [hz]
    exact Subtype.prop _

/-- **Isomorphisms of Ehresmann connections.** If a pair of `C^m` diffeomorphisms, `m ≠ 0`, is a
morphism of Ehresmann connections, then so is the pair of inverse diffeomorphisms. -/
theorem symm [IsManifold I 1 P] [IsManifold I' 1 Q] {n n' m : ℕ∞ω}
    {Ψ : P ≃ₘ^m⟮I, I'⟯ Q} {ψ : B ≃ₘ^m⟮J, J'⟯ C}
    (h : IsEhresmannConnectionHom I J I' J' π D ρ D' Ψ ψ)
    (hD : IsEhresmannConnection I J n π D) (hD' : IsEhresmannConnection I' J' n' ρ D')
    (hm : m ≠ 0) : IsEhresmannConnectionHom I' J' I J ρ D' π D Ψ.symm ψ.symm :=
  h.inverse hD hD' (Ψ.symm.mdifferentiable hm) (ψ.symm.mdifferentiable hm) Ψ.symm_apply_apply
    Ψ.apply_symm_apply ψ.symm_apply_apply

end IsEhresmannConnectionHom

end TauCeti
