/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# Products of finite toric fans

The cones `σ × τ`, for `σ` and `τ` ranging through two fans, form a fan in the product
lattice. Faces of a product cone split uniquely as products of faces of its factors, which gives
the face-closure axiom. Intersections and supports are computed componentwise.

Products preserve completeness and regularity. They also act on fan morphisms by taking the
componentwise maps, compatibly with identities and composition. These facts supply the
combinatorial product operation used by products of toric realizations.

## Main declarations

* `TauCeti.Toric.Fan.prod`: the product of two finite toric fans.
* `TauCeti.Toric.Fan.support_prod`: the support of a product is the product of the supports.
* `TauCeti.Toric.Fan.isComplete_prod_iff`: a product fan is complete exactly when both factors
  are complete.
* `TauCeti.Toric.Fan.IsRegular.prod`: products preserve regularity.
* `TauCeti.Toric.FanHom.prod`: the componentwise product of two fan morphisms.

## References

The construction is described in §1.4 of W. Fulton, *Introduction to Toric Varieties*, and
§3.1 of D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}

namespace Fan

variable (Φ : Fan i) (Ψ : Fan i')

/-! ### Product fans -/

/-- The product of two finite fans consists of the products of their cones. -/
def prod : Fan (i.prodMap i') where
  lattice := Φ.lattice.prod Ψ.lattice
  cones := (fun p : PointedCone ℝ V × PointedCone ℝ V' ↦ p.1.prod p.2) ''
    (Φ.cones ×ˢ Ψ.cones)
  finite_cones := (Φ.finite_cones.prod Ψ.finite_cones).image _
  isToricCone σ hσ := by
    obtain ⟨⟨τ, υ⟩, ⟨hτ, hυ⟩, rfl⟩ := hσ
    exact (Φ.isToricCone hτ).prod (Ψ.isToricCone hυ)
  mem_of_isFaceOf σ τ hσ hτ := by
    obtain ⟨⟨υ, ω⟩, ⟨hυ, hω⟩, rfl⟩ := hσ
    refine ⟨⟨τ.map (.fst ℝ V V'), τ.map (.snd ℝ V V')⟩,
      ⟨Φ.mem_of_isFaceOf hυ hτ.fst, Ψ.mem_of_isFaceOf hω hτ.snd⟩, ?_⟩
    ext x
    simp only [Submodule.mem_prod, PointedCone.mem_map, LinearMap.fst_apply, Prod.exists,
      exists_and_right, exists_eq_right, LinearMap.snd_apply]
    constructor
    · simp only [and_imp, forall_exists_index]
      intro y hy z hz
      have hyz := τ.add_mem hz hy
      simp only [Prod.mk_add_mk, add_comm] at hyz
      rw [← Prod.mk_add_mk, add_comm] at hyz
      refine hτ.mem_of_add_mem_left ?_ ?_ hyz
      · exact ⟨(Submodule.mem_prod.mp (hτ.le hy)).1, (Submodule.mem_prod.mp (hτ.le hz)).2⟩
      · exact ⟨(Submodule.mem_prod.mp (hτ.le hz)).1, (Submodule.mem_prod.mp (hτ.le hy)).2⟩
    · intro hx
      exact ⟨⟨x.2, hx⟩, ⟨x.1, hx⟩⟩
  inf_isFaceOf_left σ τ hσ hτ := by
    obtain ⟨⟨σ₁, τ₁⟩, ⟨hσ₁, hτ₁⟩, rfl⟩ := hσ
    obtain ⟨⟨σ₂, τ₂⟩, ⟨hσ₂, hτ₂⟩, rfl⟩ := hτ
    simpa only [Submodule.prod_inf_prod] using
      (Φ.inf_isFaceOf_left hσ₁ hσ₂).prod (Ψ.inf_isFaceOf_left hτ₁ hτ₂)

/-- The cones of a product fan are exactly the products of cones from the two factors. -/
@[simp]
theorem mem_prod_cones {ξ : PointedCone ℝ (V × V')} :
    ξ ∈ (Φ.prod Ψ).cones ↔
      ∃ σ ∈ Φ.cones, ∃ τ ∈ Ψ.cones, ξ = σ.prod τ := by
  constructor
  · rintro ⟨⟨σ, τ⟩, ⟨hσ, hτ⟩, rfl⟩
    exact ⟨σ, hσ, τ, hτ, rfl⟩
  · rintro ⟨σ, hσ, τ, hτ, rfl⟩
    exact ⟨⟨σ, τ⟩, ⟨hσ, hτ⟩, rfl⟩

/-- The support of a product fan is the product of the supports of its factors. -/
@[simp]
theorem support_prod : (Φ.prod Ψ).support = Φ.support ×ˢ Ψ.support := by
  ext x
  constructor
  · intro hx
    obtain ⟨ξ, hξ, hxξ⟩ := (Φ.prod Ψ).mem_support.1 hx
    obtain ⟨σ, hσ, τ, hτ, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
    exact ⟨Φ.mem_support.2 ⟨σ, hσ, hxξ.1⟩, Ψ.mem_support.2 ⟨τ, hτ, hxξ.2⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨σ, hσ, hxσ⟩ := Φ.mem_support.1 hx
    obtain ⟨τ, hτ, hyτ⟩ := Ψ.mem_support.1 hy
    exact (Φ.prod Ψ).mem_support.2
      ⟨σ.prod τ, (Φ.mem_prod_cones Ψ).2 ⟨σ, hσ, τ, hτ, rfl⟩, ⟨hxσ, hyτ⟩⟩

/-- A product fan is complete exactly when both factors are complete. -/
@[simp]
theorem isComplete_prod_iff : (Φ.prod Ψ).IsComplete ↔ Φ.IsComplete ∧ Ψ.IsComplete := by
  constructor
  · intro h
    constructor
    · apply Φ.isComplete_iff.2
      intro x
      obtain ⟨ξ, hξ, hxξ⟩ := (Φ.prod Ψ).isComplete_iff.1 h (x, 0)
      obtain ⟨σ, hσ, τ, _, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
      exact ⟨σ, hσ, hxξ.1⟩
    · apply Ψ.isComplete_iff.2
      intro y
      obtain ⟨ξ, hξ, hyξ⟩ := (Φ.prod Ψ).isComplete_iff.1 h (0, y)
      obtain ⟨σ, _, τ, hτ, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
      exact ⟨τ, hτ, hyξ.2⟩
  · rintro ⟨hΦ, hΨ⟩
    apply (Φ.prod Ψ).isComplete_iff.2
    rintro ⟨x, y⟩
    obtain ⟨σ, hσ, hxσ⟩ := Φ.isComplete_iff.1 hΦ x
    obtain ⟨τ, hτ, hyτ⟩ := Ψ.isComplete_iff.1 hΨ y
    exact ⟨σ.prod τ, (Φ.mem_prod_cones Ψ).2 ⟨σ, hσ, τ, hτ, rfl⟩, ⟨hxσ, hyτ⟩⟩

/-- The product of complete fans is complete. -/
theorem IsComplete.prod (hΦ : Φ.IsComplete) (hΨ : Ψ.IsComplete) : (Φ.prod Ψ).IsComplete :=
  (Φ.isComplete_prod_iff Ψ).2 ⟨hΦ, hΨ⟩

/-- The product of regular fans is regular. -/
theorem IsRegular.prod (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) : (Φ.prod Ψ).IsRegular := by
  rw [isRegular_iff]
  intro ξ hξ
  obtain ⟨σ, hσ, τ, hτ, rfl⟩ := (Φ.mem_prod_cones Ψ).1 hξ
  exact ((isRegular_iff.mp hΦ) σ hσ).prod ((isRegular_iff.mp hΨ) τ hτ)

end Fan

/-! ### Products of fan morphisms -/

namespace FanHom

variable {N₁ N₂ N₁' N₂' V₁ V₂ V₁' V₂' : Type*}
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₁'] [AddCommGroup N₂']
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₁'] [AddCommGroup V₂']
  [Module ℝ V₁] [Module ℝ V₂] [Module ℝ V₁'] [Module ℝ V₂']
  {i₁ : N₁ →+ V₁} {i₂ : N₂ →+ V₂} {i₁' : N₁' →+ V₁'} {i₂' : N₂' →+ V₂'}
  {Φ₁ : Fan i₁} {Φ₂ : Fan i₂} {Ψ₁ : Fan i₁'} {Ψ₂ : Fan i₂'}

/-- The product of two fan morphisms is given by the componentwise maps. -/
def prod (f : FanHom Φ₁ Ψ₁) (g : FanHom Φ₂ Ψ₂) : FanHom (Φ₁.prod Φ₂) (Ψ₁.prod Ψ₂) where
  latticeMap := f.latticeMap.prodMap g.latticeMap
  realMap := f.realMap.prodMap g.realMap
  map_lattice n := by
    change (f.realMap (i₁ n.1), g.realMap (i₂ n.2)) =
      (i₁' (f.latticeMap n.1), i₂' (g.latticeMap n.2))
    rw [f.map_lattice, g.map_lattice]
  map_cone ξ hξ := by
    obtain ⟨σ, hσ, τ, hτ, rfl⟩ := (Φ₁.mem_prod_cones Φ₂).1 hξ
    obtain ⟨σ', hσ', hleσ⟩ := f.map_cone hσ
    obtain ⟨τ', hτ', hleτ⟩ := g.map_cone hτ
    refine ⟨σ'.prod τ', (Ψ₁.mem_prod_cones Ψ₂).2 ⟨σ', hσ', τ', hτ', rfl⟩, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨hleσ ⟨x.1, hx.1, rfl⟩, hleτ ⟨x.2, hx.2, rfl⟩⟩

/-- The integral map of a product morphism is the product of the integral maps. -/
@[simp]
theorem prod_latticeMap (f : FanHom Φ₁ Ψ₁) (g : FanHom Φ₂ Ψ₂) :
    (f.prod g).latticeMap = f.latticeMap.prodMap g.latticeMap := by
  rw [prod]

/-- The real-linear map of a product morphism is the product of the real-linear maps. -/
@[simp]
theorem prod_realMap (f : FanHom Φ₁ Ψ₁) (g : FanHom Φ₂ Ψ₂) :
    (f.prod g).realMap = f.realMap.prodMap g.realMap := by
  rw [prod]

/-- Products of identity fan morphisms are identity fan morphisms. -/
@[simp]
theorem prod_id : (FanHom.id Φ₁).prod (FanHom.id Φ₂) = FanHom.id (Φ₁.prod Φ₂) := by
  apply FanHom.ext
  simp only [prod_latticeMap, id_latticeMap]
  ext x <;> rfl

section Comp

variable {N₁'' N₂'' V₁'' V₂'' : Type*} [AddCommGroup N₁''] [AddCommGroup N₂'']
  [AddCommGroup V₁''] [AddCommGroup V₂''] [Module ℝ V₁''] [Module ℝ V₂'']
  {i₁'' : N₁'' →+ V₁''} {i₂'' : N₂'' →+ V₂''} {Ω₁ : Fan i₁''} {Ω₂ : Fan i₂''}

/-- Products commute with composition of fan morphisms. -/
theorem prod_comp (f₁ : FanHom Φ₁ Ψ₁) (f₂ : FanHom Ψ₁ Ω₁) (g₁ : FanHom Φ₂ Ψ₂)
    (g₂ : FanHom Ψ₂ Ω₂) :
    (f₂.comp f₁).prod (g₂.comp g₁) = (f₂.prod g₂).comp (f₁.prod g₁) := by
  apply FanHom.ext
  simp only [prod_latticeMap, comp_latticeMap]
  ext x <;> rfl

end Comp

end FanHom

end TauCeti.Toric
