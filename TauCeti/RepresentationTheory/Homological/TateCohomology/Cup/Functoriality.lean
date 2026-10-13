/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta

/-!
# The Tate cup product along an isomorphism of finite groups

A compatible pair `(e, φ)`, a group isomorphism `e : G ≃* H` together with a linear map `φ` from a
`G`-representation `M` to an `H`-representation `N` satisfying `φ ∘ ρ g = σ (e g) ∘ φ`, induces a
map `TauCeti.TateCohomology.map` on Tate cohomology in every degree. This file proves that these
maps are compatible with the Tate cup product in all integer bidegrees
(`TauCeti.TateCohomology.map_cup`): for compatible pairs `(e, φ₁)` and `(e, φ₂)`, the pair
`(e, φ₁ ⊗ φ₂)` carries `x ∪ y` to the cup product of the images of `x` and `y`.

The main application is conjugation of a finite normal layer of a class formation, under which
cup product with the fundamental class, and hence the Artin map, is equivariant.

## Main statements

* `TauCeti.TateCohomology.map_cup`: every pair of compatible pairs along the same isomorphism is
  compatible with the cup product.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter V, §3 and Chapter VI, §5.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Chapter I, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep Representation

namespace TauCeti.TateCohomology

/-
Every compatible pair factors as a morphism of `G`-representations `M ⟶ Res(e)(N)` followed by the
pair `Res(e)(N) → N` whose linear part is the identity
(`TauCeti.TateCohomology.tateCohomologyFunctor_map_comp_map_res`), and the cup product is already
natural in morphisms of coefficients. The main step is therefore the pair `Res(e)(N) → N`. It is
proved like the restriction law `TauCeti.TateCohomology.cup_res`, by induction on
the degree of the second factor: in degree zero both cup products are induced by the morphism
`m ↦ m ⊗ y` for an invariant `y`, and the rule `x ∪ δ y = (-1)^p δ (x ∪ y)` for the `k`-split
dimension-shifting sequences moves the statement up and down in degree, because these maps commute
with the connecting maps in every degree (`TauCeti.TateCohomology.δ_comp_map`). Unlike restriction
to a subgroup, an isomorphism of groups induces a map of Tate complexes, so negative degrees need
no separate low-degree computation.
-/

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [Fintype G] [Fintype H]

section Res

variable (e : G ≃* H) (N₁ : Rep k H)

/-- The connecting maps of a short exact sequence of `H`-representations and of its restriction
along `e` are intertwined by the pairs `Res(e)(N) → N`. -/
private theorem δ_comp_map_res {S : ShortComplex (Rep k H)} (hS : S.ShortExact) (r : ℤ) :
    _root_.TateCohomology.δ ((shortExact_res (e : G →* H)).2 hS) r ≫
        map (Rep.isIntertwiningMap_res S.X₁ (e : G →* H)) (r + 1) =
      map (Rep.isIntertwiningMap_res S.X₃ (e : G →* H)) r ≫ _root_.TateCohomology.δ hS r :=
  δ_comp_map _ hS _ (Rep.isIntertwiningMap_res S.X₂ (e : G →* H)) _ (by ext; rfl) (by ext; rfl) r

/-- The connecting maps of the tensor product with `N₁` of a `k`-split short exact sequence of
`H`-representations and of its restriction along `e` are intertwined by the tensor pairs. -/
private theorem δ_comp_resTensorMap {D : ShortComplex (Rep k H)} (hD : D.ShortExact)
    {r : D.X₂.V →ₗ[k] D.X₁.V} (hr : Function.LeftInverse r D.f.hom) (n : ℤ) :
    _root_.TateCohomology.δ (haveI := ((shortExact_res (e : G →* H)).2 hD).epi_g;
      shortExact_map_tensorLeft_of_leftInverse ((shortExact_res (e : G →* H)).2 hD).exact
        (Rep.res (e : G →* H) N₁) hr) n ≫
        map (Rep.isIntertwiningMap_tensor_res N₁ D.X₁ (e : G →* H)) (n + 1) =
      map (Rep.isIntertwiningMap_tensor_res N₁ D.X₃ (e : G →* H)) n ≫ _root_.TateCohomology.δ
        (haveI := hD.epi_g; shortExact_map_tensorLeft_of_leftInverse hD.exact N₁ hr) n := by
  have := hD.epi_g
  have := ((shortExact_res (e : G →* H)).2 hD).epi_g
  exact δ_comp_map
    (S := (D.map (resFunctor (e : G →* H))).map (tensorLeft (Rep.res (e : G →* H) N₁)))
    (S' := D.map (tensorLeft N₁))
    (shortExact_map_tensorLeft_of_leftInverse ((shortExact_res (e : G →* H)).2 hD).exact
      (Rep.res (e : G →* H) N₁) hr)
    (shortExact_map_tensorLeft_of_leftInverse hD.exact N₁ hr)
    (Rep.isIntertwiningMap_tensor_res N₁ D.X₁ (e : G →* H))
    (Rep.isIntertwiningMap_tensor_res N₁ D.X₂ (e : G →* H))
    (Rep.isIntertwiningMap_tensor_res N₁ D.X₃ (e : G →* H)) (TensorProduct.ext' fun _ _ ↦ rfl)
    (TensorProduct.ext' fun _ _ ↦ rfl) n

/-- In bidegree `(p, 0)`: the cup product with the class of an invariant `y` is induced by the
morphism `m ↦ m ⊗ y`, and the pairs `Res(e)(N) → N` are natural in such morphisms. -/
private theorem cupH0_map_res (N₂ : Rep k H) (p : ℤ)
    (x : tateCohomology (Rep.res (e : G →* H) N₁) p)
    (y : tateCohomology (Rep.res (e : G →* H) N₂) 0) :
    map (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H)) p
        (cupH0 (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) N₂) p x y) =
      cupH0 N₁ N₂ p (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
        (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) 0 y) := by
  induction y using H0_induction_on with
  | h v =>
    rw [cupH0_H0π, H0π_comp_map_apply, cupH0_H0π]
    -- The morphism `m ↦ m ⊗ v` of `G`-representations is the restriction of the morphism
    -- `m ↦ m ⊗ v` of `H`-representations.
    refine ConcreteCategory.congr_hom (tateCohomologyFunctor_map_comp_map
      (Rep.isIntertwiningMap_res N₁ (e : G →* H))
      (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H))
      (Rep.tensorInvariant (Rep.res (e : G →* H) N₁) v)
      (Rep.tensorInvariant N₁ (mapInvariants (Rep.isIntertwiningMap_res N₂ (e : G →* H)) v))
      ?_ p) x
    ext m
    refine (congrArg (TensorProduct.map _ _) (Rep.tensorInvariant_hom_apply _ v m)).trans ?_
    refine Eq.trans ?_ (Rep.tensorInvariant_hom_apply N₁ _ m).symm
    rw [TensorProduct.map_tmul, mapInvariants_apply_coe]
    rfl

/-- On the source group, transport of `x ∪ δ y` is `(-1)^p δ` of the transport of `x ∪ y`, for
a sequence `D` of `H`-representations split by `r`. -/
private theorem map_res_cup_δ {D : ShortComplex (Rep k H)} (hD : D.ShortExact)
    {r : D.X₂.V →ₗ[k] D.X₁.V} (hr : Function.LeftInverse r D.f.hom) {p q n : ℤ} (h : p + q = n)
    (x : tateCohomology (Rep.res (e : G →* H) N₁) p)
    (y : tateCohomology (Rep.res (e : G →* H) D.X₃) q) :
    map (Rep.isIntertwiningMap_tensor_res N₁ D.X₁ (e : G →* H)) (n + 1)
        (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) D.X₁) p (q + 1) (n + 1) (by omega) x
          (_root_.TateCohomology.δ ((shortExact_res (e : G →* H)).2 hD) q y)) =
      p.negOnePow • _root_.TateCohomology.δ
        (haveI := hD.epi_g; shortExact_map_tensorLeft_of_leftInverse hD.exact N₁ hr) n
        (map (Rep.isIntertwiningMap_tensor_res N₁ D.X₃ (e : G →* H)) n
          (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) D.X₃) p q n h x y)) := by
  -- `x ∪ δ y = (-1)^p δ (x ∪ y)` for the restricted sequence, which is still split by `r`.
  have hG := cup_δ_of_leftInverse (Rep.res (e : G →* H) N₁) ((shortExact_res (e : G →* H)).2 hD)
    (r := r) hr h x y
  refine (congrArg
    (map (Rep.isIntertwiningMap_tensor_res N₁ D.X₁ (e : G →* H)) (n + 1)) hG).trans ?_
  rw [Units.smul_def, map_zsmul, Units.smul_def]
  exact congrArg ((p.negOnePow : ℤ) • ·)
    (ConcreteCategory.congr_hom (δ_comp_resTensorMap e N₁ hD hr n) _)

/-- On the target group, `x ∪` the transport of `δ y` is `(-1)^p δ (x ∪` the transport of `y)`,
for a sequence `D` of `H`-representations split by `r`. -/
private theorem cup_map_res_δ {D : ShortComplex (Rep k H)} (hD : D.ShortExact)
    {r : D.X₂.V →ₗ[k] D.X₁.V} (hr : Function.LeftInverse r D.f.hom) {p q n : ℤ} (h : p + q = n)
    (x : tateCohomology N₁ p) (y : tateCohomology (Rep.res (e : G →* H) D.X₃) q) :
    cup N₁ D.X₁ p (q + 1) (n + 1) (by omega) x
        (map (Rep.isIntertwiningMap_res D.X₁ (e : G →* H)) (q + 1)
          (_root_.TateCohomology.δ ((shortExact_res (e : G →* H)).2 hD) q y)) =
      p.negOnePow • _root_.TateCohomology.δ
        (haveI := hD.epi_g; shortExact_map_tensorLeft_of_leftInverse hD.exact N₁ hr) n
        (cup N₁ D.X₃ p q n h x (map (Rep.isIntertwiningMap_res D.X₃ (e : G →* H)) q y)) := by
  rw [← ModuleCat.comp_apply, δ_comp_map_res e hD, ModuleCat.comp_apply]
  exact cup_δ_of_leftInverse N₁ hD hr h x _

/-- The base case: bidegree `(p, 0)`. -/
private theorem map_res_cup_zero_right (N₂ : Rep k H) {p r : ℤ} (h : p + 0 = r)
    (x : tateCohomology (Rep.res (e : G →* H) N₁) p)
    (y : tateCohomology (Rep.res (e : G →* H) N₂) 0) :
    map (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H)) r
        (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) N₂) p 0 r h x y) =
      cup N₁ N₂ p 0 r h (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
        (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) 0 y) := by
  obtain rfl : p = r := by omega
  rw [cup_zero_right, cup_zero_right]
  exact cupH0_map_res e N₁ N₂ p x y

/-- The upward step: every class of degree `q + 1` of the restriction is a connecting image from
the restricted upward shift, so the claim in degree `q` for the upward shift gives it in degree
`q + 1`. -/
private theorem map_res_cup_add_one (N₂ : Rep k H) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology (Rep.res (e : G →* H) N₁) p)
    (ih : ∀ y : tateCohomology (Rep.res (e : G →* H) (dimensionShiftUp N₂)) q,
      map (Rep.isIntertwiningMap_tensor_res N₁ (dimensionShiftUp N₂) (e : G →* H)) r
          (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) (dimensionShiftUp N₂)) p q r h
            x y) =
        cup N₁ (dimensionShiftUp N₂) p q r h (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
          (map (Rep.isIntertwiningMap_res (dimensionShiftUp N₂) (e : G →* H)) q y))
    (y : tateCohomology (Rep.res (e : G →* H) N₂) (q + 1)) :
    map (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H)) (r + 1)
        (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) N₂) p (q + 1) (r + 1) (by omega)
          x y) =
      cup N₁ N₂ p (q + 1) (r + 1) (by omega) (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
        (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) (q + 1) y) := by
  let D := ShortComplex.mk (coindBotUnit N₂) (dimensionShiftUpπ N₂)
    (coindBotUnit_comp_dimensionShiftUpπ N₂)
  have hD : D.ShortExact := by
    simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N₂
  -- Write `y` as the connecting image of a class `y'` of the restricted upward shift: transport
  -- is an isomorphism commuting with the connecting maps, and the connecting map of `D` is one.
  obtain ⟨y', rfl⟩ :
      ∃ y', _root_.TateCohomology.δ ((shortExact_res (e : G →* H)).2 hD) q y' = y := by
    refine ⟨(mapIso (Rep.isIntertwiningMap_res (dimensionShiftUp N₂) (e : G →* H)) q).inv
      ((dimensionShiftUpIso N₂ q).inv
        (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) (q + 1) y)), ?_⟩
    have hinj : Function.Injective (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) (q + 1)) := by
      rw [← mapIso_hom]
      exact (ModuleCat.mono_iff_injective _).1 inferInstance
    apply hinj
    rw [← ModuleCat.comp_apply, δ_comp_map_res e hD, ModuleCat.comp_apply, ← mapIso_hom,
      Iso.inv_hom_id_apply, ← dimensionShiftUpIso_hom, Iso.inv_hom_id_apply]
  rw [map_res_cup_δ e N₁ hD (leftInverse_coindBotUnit N₂) h x y', ih,
    cup_map_res_δ e N₁ hD (leftInverse_coindBotUnit N₂) h]

/-- The downward step: the connecting map of the tensored downward shift is injective, so the
claim in degree `q + 1` for the downward shift gives it in degree `q`. -/
private theorem map_res_cup_of_add_one (N₂ : Rep k H) {p q r : ℤ} (h : p + q = r)
    (x : tateCohomology (Rep.res (e : G →* H) N₁) p)
    (ih : ∀ y : tateCohomology (Rep.res (e : G →* H) (dimensionShiftDown N₂)) (q + 1),
      map (Rep.isIntertwiningMap_tensor_res N₁ (dimensionShiftDown N₂) (e : G →* H)) (r + 1)
          (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) (dimensionShiftDown N₂)) p (q + 1)
            (r + 1) (by omega) x y) =
        cup N₁ (dimensionShiftDown N₂) p (q + 1) (r + 1) (by omega)
          (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
          (map (Rep.isIntertwiningMap_res (dimensionShiftDown N₂) (e : G →* H)) (q + 1) y))
    (y : tateCohomology (Rep.res (e : G →* H) N₂) q) :
    map (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H)) r
        (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) N₂) p q r h x y) =
      cup N₁ N₂ p q r h (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
        (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) q y) := by
  let D := ShortComplex.mk (dimensionShiftDownι N₂) (indBotCounit N₂)
    (dimensionShiftDownι_comp_indBotCounit N₂)
  have hD : D.ShortExact := by
    simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact N₂
  have := hD.mono_f
  obtain ⟨s, hs⟩ := exists_leftInverse_of_rightInverse hD.exact (rightInverse_indBotCounit N₂)
  -- The connecting map of `N₁ ⊗ D` in degree `r` is the tensored downward shift, an isomorphism.
  have hinj : Function.Injective (_root_.TateCohomology.δ
      (haveI := hD.epi_g; shortExact_map_tensorLeft_of_leftInverse hD.exact N₁ hs) r) := by
    have hiso : (tensorDimensionShiftDownIso N₂ N₁ r (r + 1) rfl).hom =
        _root_.TateCohomology.δ
          (haveI := hD.epi_g; shortExact_map_tensorLeft_of_leftInverse hD.exact N₁ hs) r :=
      tensorDimensionShiftDownIso_hom N₂ N₁ r (r + 1) rfl
    rw [← hiso]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  have key := ih (_root_.TateCohomology.δ ((shortExact_res (e : G →* H)).2 hD) q y)
  rw [map_res_cup_δ e N₁ hD hs h x y, cup_map_res_δ e N₁ hD hs h _ y] at key
  exact smul_left_cancel _ key

/-- The cup product commutes with the pairs `Res(e)(N) → N`, in every bidegree. -/
private theorem map_res_cup (N₂ : Rep k H) (p q r : ℤ) (h : p + q = r)
    (x : tateCohomology (Rep.res (e : G →* H) N₁) p)
    (y : tateCohomology (Rep.res (e : G →* H) N₂) q) :
    map (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H)) r
        (cup (Rep.res (e : G →* H) N₁) (Rep.res (e : G →* H) N₂) p q r h x y) =
      cup N₁ N₂ p q r h (map (Rep.isIntertwiningMap_res N₁ (e : G →* H)) p x)
        (map (Rep.isIntertwiningMap_res N₂ (e : G →* H)) q y) := by
  rcases le_or_gt 0 q with hq | hq
  · induction q, hq using Int.leInduction generalizing N₂ r with
    | base => exact map_res_cup_zero_right e N₁ N₂ h x y
    | succ q _ ih =>
      obtain rfl : r = p + q + 1 := by omega
      exact map_res_cup_add_one e N₁ N₂ rfl x (ih (dimensionShiftUp N₂) _ rfl) y
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    clear hq
    induction n generalizing N₂ r with
    | zero =>
      -- `Int.negSucc 0 + 1` is `0` by definition.
      exact map_res_cup_of_add_one e N₁ N₂ h x
        (fun y' ↦ map_res_cup_zero_right e N₁ (dimensionShiftDown N₂) (by omega) x y') y
    | succ n ih =>
      -- `Int.negSucc (n + 1) + 1` is `Int.negSucc n` by definition.
      exact map_res_cup_of_add_one e N₁ N₂ h x
        (fun y' ↦ ih (dimensionShiftDown N₂) _ (by omega) y') y

end Res

/-- **The Tate cup product is natural along compatible pairs.** For compatible pairs `(e, φ₁)` from
`M₁` to `N₁` and `(e, φ₂)` from `M₂` to `N₂` along one isomorphism `e : G ≃* H` of finite groups,
the pair `(e, φ₁ ⊗ φ₂)` carries `x ∪ y` to the cup product of the images of `x` and `y`, in every
bidegree. -/
theorem map_cup {e : G ≃* H} {M₁ M₂ : Rep k G} {N₁ N₂ : Rep k H} {φ₁ : M₁.V →ₗ[k] N₁.V}
    {φ₂ : M₂.V →ₗ[k] N₂.V} (h₁ : M₁.ρ.IsIntertwiningMap (N₁.ρ.comp (e : G →* H)) φ₁)
    (h₂ : M₂.ρ.IsIntertwiningMap (N₂.ρ.comp (e : G →* H)) φ₂) (p q r : ℤ) (h : p + q = r)
    (x : tateCohomology M₁ p) (y : tateCohomology M₂ q) :
    map (h₁.tensor h₂) r (cup M₁ M₂ p q r h x y) =
      cup N₁ N₂ p q r h (map h₁ p x) (map h₂ q y) := by
  -- Factor each pair through the restriction of its target; the factor of the tensor pair is the
  -- tensor product of the factors of the two pairs.
  let f₁ := IsIntertwiningMap.toRes h₁
  let f₂ := IsIntertwiningMap.toRes h₂
  have hf := tateCohomologyFunctor_map_comp_map (h₁.tensor h₂)
    (Rep.isIntertwiningMap_tensor_res N₁ N₂ (e : G →* H))
    (f₁ ▷ M₂ ≫ Rep.res (e : G →* H) N₁ ◁ f₂) (𝟙 (N₁ ⊗ N₂))
    (TensorProduct.ext' fun a b ↦ by simp [f₁, f₂]) r
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hf
  rw [← hf,
    ← tateCohomologyFunctor_map_comp_map_res h₁ f₁ (IsIntertwiningMap.toRes_hom_toLinearMap h₁),
    ← tateCohomologyFunctor_map_comp_map_res h₂ f₂ (IsIntertwiningMap.toRes_hom_toLinearMap h₂),
    ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply, ← map_res_cup,
    CategoryTheory.Functor.map_comp, ModuleCat.comp_apply, ← cup_map_left, ← cup_map_right]

end TauCeti.TateCohomology
