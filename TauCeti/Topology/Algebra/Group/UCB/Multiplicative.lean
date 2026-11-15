/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ContinuousMonoidHom.TypeTags
public import TauCeti.Topology.Algebra.Group.UCB.CompRight

/-!
# Bounded uniformly continuous functions on `Multiplicative` and `Additive` type tags

For an additive topological group `A`, precomposition with `Multiplicative.ofAdd` and
`Multiplicative.toAdd` identifies `TauCeti.UCB (Multiplicative A)` with `TauCeti.AddUCB A` as unital
real Banach algebras and ordered vector spaces, intertwining left and right translations and
pullbacks along continuous homomorphisms. Dually, `TauCeti.AddUCB (Additive G)` is identified with
`TauCeti.UCB G` for a multiplicative topological group `G`.

## Main definitions

* `TauCeti.UCB.multiplicativeAlgEquiv A`: `UCB (Multiplicative A) ≃ₐ[ℝ] AddUCB A`.
* `TauCeti.UCB.multiplicativeLinearIsometryEquiv A`: `UCB (Multiplicative A) ≃ₗᵢ[ℝ] AddUCB A`.
* `TauCeti.AddUCB.additiveAlgEquiv G`: `AddUCB (Additive G) ≃ₐ[ℝ] UCB G`.
* `TauCeti.AddUCB.additiveLinearIsometryEquiv G`: `AddUCB (Additive G) ≃ₗᵢ[ℝ] UCB G`.
-/

public section

noncomputable section

open Additive (ofMul toMul)
open Filter
open Multiplicative (ofAdd toAdd)
open scoped BoundedContinuousFunction Topology

namespace TauCeti

section Multiplicative

variable {𝕜 A B : Type*} [NormedField 𝕜]
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Precomposing a function in `ucbSubalgebra 𝕜 (Multiplicative A)` with `ofAdd` yields a function
in `addUcbSubalgebra 𝕜 A`. -/
theorem compContinuous_ofAdd_mem_addUcbSubalgebra {f : Multiplicative A →ᵇ 𝕜}
    (hf : f ∈ ucbSubalgebra 𝕜 (Multiplicative A)) :
    f.compContinuous ⟨ofAdd, continuous_ofAdd⟩ ∈ addUcbSubalgebra 𝕜 A := by
  rw [mem_ucbSubalgebra_iff] at hf
  rw [mem_addUcbSubalgebra_iff]
  intro ε hε
  have h1 : 𝓝 (0 : A) = map toAdd (𝓝 (1 : Multiplicative A)) := nhds_toAdd 1
  rw [h1, eventually_map]
  filter_upwards [hf ε hε] with u hu x
  simpa using hu (ofAdd x)

/-- Precomposing a function in `addUcbSubalgebra 𝕜 A` with `toAdd` yields a function in
`ucbSubalgebra 𝕜 (Multiplicative A)`. -/
theorem compContinuous_toAdd_mem_ucbSubalgebra {f : A →ᵇ 𝕜} (hf : f ∈ addUcbSubalgebra 𝕜 A) :
    f.compContinuous ⟨toAdd, continuous_toAdd⟩ ∈ ucbSubalgebra 𝕜 (Multiplicative A) := by
  rw [mem_addUcbSubalgebra_iff] at hf
  rw [mem_ucbSubalgebra_iff]
  intro ε hε
  have h0 : 𝓝 (1 : Multiplicative A) = map ofAdd (𝓝 (0 : A)) := nhds_ofAdd 0
  rw [h0, eventually_map]
  filter_upwards [hf ε hε] with u hu x
  simpa using hu x.toAdd

namespace UCB

variable (A) in
/-- `UCB (Multiplicative A)` is canonically isomorphic as a real algebra to `AddUCB A`. -/
def multiplicativeAlgEquiv : UCB (Multiplicative A) ≃ₐ[ℝ] AddUCB A where
  toFun f :=
    ⟨(f : Multiplicative A →ᵇ ℝ).compContinuous ⟨ofAdd, continuous_ofAdd⟩,
      compContinuous_ofAdd_mem_addUcbSubalgebra f.2⟩
  invFun f :=
    ⟨(f : A →ᵇ ℝ).compContinuous ⟨toAdd, continuous_toAdd⟩,
      compContinuous_toAdd_mem_ucbSubalgebra f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem multiplicativeAlgEquiv_apply (f : UCB (Multiplicative A)) (x : A) :
    (multiplicativeAlgEquiv A f : A →ᵇ ℝ) x = (f : Multiplicative A →ᵇ ℝ) (ofAdd x) :=
  (rfl)

@[simp]
theorem multiplicativeAlgEquiv_symm_apply (f : AddUCB A) (x : Multiplicative A) :
    ((multiplicativeAlgEquiv A).symm f : Multiplicative A →ᵇ ℝ) x = (f : A →ᵇ ℝ) x.toAdd :=
  (rfl)

@[simp]
theorem multiplicativeAlgEquiv_le_iff {f g : UCB (Multiplicative A)} :
    multiplicativeAlgEquiv A f ≤ multiplicativeAlgEquiv A g ↔ f ≤ g :=
  ⟨fun h => le_def.2 fun x => AddUCB.le_def.1 h x.toAdd,
    fun h => AddUCB.le_def.2 fun x => le_def.1 h (ofAdd x)⟩

@[simp]
theorem multiplicativeAlgEquiv_symm_le_iff {f g : AddUCB A} :
    (multiplicativeAlgEquiv A).symm f ≤ (multiplicativeAlgEquiv A).symm g ↔ f ≤ g :=
  ⟨fun h => AddUCB.le_def.2 fun x => le_def.1 h (ofAdd x),
    fun h => le_def.2 fun x => AddUCB.le_def.1 h x.toAdd⟩

/-- `multiplicativeAlgEquiv` preserves the supremum norm. -/
theorem norm_multiplicativeAlgEquiv (f : UCB (Multiplicative A)) :
    ‖multiplicativeAlgEquiv A f‖ = ‖f‖ := by
  refine le_antisymm ((f : Multiplicative A →ᵇ ℝ).norm_compContinuous_le _) ?_
  exact ((multiplicativeAlgEquiv A f : A →ᵇ ℝ).norm_compContinuous_le ⟨toAdd, continuous_toAdd⟩)

@[simp]
theorem norm_coe_multiplicativeAlgEquiv (f : UCB (Multiplicative A)) :
    ‖(multiplicativeAlgEquiv A f : A →ᵇ ℝ)‖ = ‖(f : Multiplicative A →ᵇ ℝ)‖ :=
  norm_multiplicativeAlgEquiv f

/-- `(multiplicativeAlgEquiv _).symm` preserves the supremum norm. -/
theorem norm_multiplicativeAlgEquiv_symm (f : AddUCB A) :
    ‖(multiplicativeAlgEquiv A).symm f‖ = ‖f‖ := by
  simpa using (norm_multiplicativeAlgEquiv ((multiplicativeAlgEquiv A).symm f)).symm

@[simp]
theorem norm_coe_multiplicativeAlgEquiv_symm (f : AddUCB A) :
    ‖((multiplicativeAlgEquiv A).symm f : Multiplicative A →ᵇ ℝ)‖ = ‖(f : A →ᵇ ℝ)‖ :=
  norm_multiplicativeAlgEquiv_symm f

variable (A) in
/-- `UCB (Multiplicative A)` is canonically isometric as a real Banach space to `AddUCB A`. -/
def multiplicativeLinearIsometryEquiv : UCB (Multiplicative A) ≃ₗᵢ[ℝ] AddUCB A where
  toLinearEquiv := (multiplicativeAlgEquiv A).toLinearEquiv
  norm_map' := norm_multiplicativeAlgEquiv

@[simp]
theorem multiplicativeLinearIsometryEquiv_apply (f : UCB (Multiplicative A)) :
    multiplicativeLinearIsometryEquiv A f = multiplicativeAlgEquiv A f :=
  (rfl)

@[simp]
theorem multiplicativeLinearIsometryEquiv_symm_apply (f : AddUCB A) :
    (multiplicativeLinearIsometryEquiv A).symm f = (multiplicativeAlgEquiv A).symm f :=
  (rfl)

@[simp]
theorem multiplicativeAlgEquiv_leftTranslation (a : A) (f : UCB (Multiplicative A)) :
    multiplicativeAlgEquiv A (leftTranslation (ofAdd a) f) =
      AddUCB.leftTranslation a (multiplicativeAlgEquiv A f) := by
  ext
  simp

@[simp]
theorem multiplicativeAlgEquiv_symm_leftTranslation (a : A) (f : AddUCB A) :
    (multiplicativeAlgEquiv A).symm (AddUCB.leftTranslation a f) =
      leftTranslation (ofAdd a) ((multiplicativeAlgEquiv A).symm f) := by
  ext
  simp

@[simp]
theorem multiplicativeAlgEquiv_rightTranslation (a : A) (f : UCB (Multiplicative A)) :
    multiplicativeAlgEquiv A (rightTranslation (ofAdd a) f) =
      AddUCB.rightTranslation a (multiplicativeAlgEquiv A f) := by
  ext
  simp

@[simp]
theorem multiplicativeAlgEquiv_symm_rightTranslation (a : A) (f : AddUCB A) :
    (multiplicativeAlgEquiv A).symm (AddUCB.rightTranslation a f) =
      rightTranslation (ofAdd a) ((multiplicativeAlgEquiv A).symm f) := by
  ext
  simp

/-- `multiplicativeAlgEquiv` intertwines pullback along `φ.toMultiplicative` with pullback along
`φ`. -/
theorem multiplicativeAlgEquiv_compRightAlgHom (φ : A →ₜ+ B) (f : UCB (Multiplicative B)) :
    multiplicativeAlgEquiv A (compRightAlgHom φ.toMultiplicative f) =
      AddUCB.compRightAlgHom φ (multiplicativeAlgEquiv B f) := by
  ext
  simp

/-- `(multiplicativeAlgEquiv _).symm` intertwines pullback along `φ` with pullback along
`φ.toMultiplicative`. -/
theorem multiplicativeAlgEquiv_symm_compRightAlgHom (φ : A →ₜ+ B) (f : AddUCB B) :
    (multiplicativeAlgEquiv A).symm (AddUCB.compRightAlgHom φ f) =
      compRightAlgHom φ.toMultiplicative ((multiplicativeAlgEquiv B).symm f) := by
  ext
  simp

end UCB

end Multiplicative

section Additive

variable {𝕜 G H : Type*} [NormedField 𝕜]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Precomposing a function in `addUcbSubalgebra 𝕜 (Additive G)` with `ofMul` yields a function in
`ucbSubalgebra 𝕜 G`. -/
theorem compContinuous_ofMul_mem_ucbSubalgebra {f : Additive G →ᵇ 𝕜}
    (hf : f ∈ addUcbSubalgebra 𝕜 (Additive G)) :
    f.compContinuous ⟨ofMul, continuous_ofMul⟩ ∈ ucbSubalgebra 𝕜 G := by
  rw [mem_addUcbSubalgebra_iff] at hf
  rw [mem_ucbSubalgebra_iff]
  intro ε hε
  have h1 : 𝓝 (1 : G) = map toMul (𝓝 (0 : Additive G)) := nhds_toMul 0
  rw [h1, eventually_map]
  filter_upwards [hf ε hε] with u hu x
  simpa using hu (ofMul x)

/-- Precomposing a function in `ucbSubalgebra 𝕜 G` with `toMul` yields a function in
`addUcbSubalgebra 𝕜 (Additive G)`. -/
theorem compContinuous_toMul_mem_addUcbSubalgebra {f : G →ᵇ 𝕜} (hf : f ∈ ucbSubalgebra 𝕜 G) :
    f.compContinuous ⟨toMul, continuous_toMul⟩ ∈ addUcbSubalgebra 𝕜 (Additive G) := by
  rw [mem_ucbSubalgebra_iff] at hf
  rw [mem_addUcbSubalgebra_iff]
  intro ε hε
  have h0 : 𝓝 (0 : Additive G) = map ofMul (𝓝 (1 : G)) := nhds_ofMul 1
  rw [h0, eventually_map]
  filter_upwards [hf ε hε] with u hu x
  simpa using hu x.toMul

namespace AddUCB

variable (G) in
/-- `AddUCB (Additive G)` is canonically isomorphic as a real algebra to `UCB G`. -/
def additiveAlgEquiv : AddUCB (Additive G) ≃ₐ[ℝ] UCB G where
  toFun f :=
    ⟨(f : Additive G →ᵇ ℝ).compContinuous ⟨ofMul, continuous_ofMul⟩,
      compContinuous_ofMul_mem_ucbSubalgebra f.2⟩
  invFun f :=
    ⟨(f : G →ᵇ ℝ).compContinuous ⟨toMul, continuous_toMul⟩,
      compContinuous_toMul_mem_addUcbSubalgebra f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem additiveAlgEquiv_apply (f : AddUCB (Additive G)) (x : G) :
    (additiveAlgEquiv G f : G →ᵇ ℝ) x = (f : Additive G →ᵇ ℝ) (ofMul x) :=
  (rfl)

@[simp]
theorem additiveAlgEquiv_symm_apply (f : UCB G) (x : Additive G) :
    ((additiveAlgEquiv G).symm f : Additive G →ᵇ ℝ) x = (f : G →ᵇ ℝ) x.toMul :=
  (rfl)

@[simp]
theorem additiveAlgEquiv_le_iff {f g : AddUCB (Additive G)} :
    additiveAlgEquiv G f ≤ additiveAlgEquiv G g ↔ f ≤ g :=
  ⟨fun h => le_def.2 fun x => UCB.le_def.1 h x.toMul,
    fun h => UCB.le_def.2 fun x => le_def.1 h (ofMul x)⟩

@[simp]
theorem additiveAlgEquiv_symm_le_iff {f g : UCB G} :
    (additiveAlgEquiv G).symm f ≤ (additiveAlgEquiv G).symm g ↔ f ≤ g :=
  ⟨fun h => UCB.le_def.2 fun x => le_def.1 h (ofMul x),
    fun h => le_def.2 fun x => UCB.le_def.1 h x.toMul⟩

/-- `additiveAlgEquiv` preserves the supremum norm. -/
theorem norm_additiveAlgEquiv (f : AddUCB (Additive G)) :
    ‖additiveAlgEquiv G f‖ = ‖f‖ := by
  refine le_antisymm ((f : Additive G →ᵇ ℝ).norm_compContinuous_le _) ?_
  exact ((additiveAlgEquiv G f : G →ᵇ ℝ).norm_compContinuous_le ⟨toMul, continuous_toMul⟩)

@[simp]
theorem norm_coe_additiveAlgEquiv (f : AddUCB (Additive G)) :
    ‖(additiveAlgEquiv G f : G →ᵇ ℝ)‖ = ‖(f : Additive G →ᵇ ℝ)‖ :=
  norm_additiveAlgEquiv f

/-- `(additiveAlgEquiv _).symm` preserves the supremum norm. -/
theorem norm_additiveAlgEquiv_symm (f : UCB G) :
    ‖(additiveAlgEquiv G).symm f‖ = ‖f‖ := by
  simpa using (norm_additiveAlgEquiv ((additiveAlgEquiv G).symm f)).symm

@[simp]
theorem norm_coe_additiveAlgEquiv_symm (f : UCB G) :
    ‖((additiveAlgEquiv G).symm f : Additive G →ᵇ ℝ)‖ = ‖(f : G →ᵇ ℝ)‖ :=
  norm_additiveAlgEquiv_symm f

variable (G) in
/-- `AddUCB (Additive G)` is canonically isometric as a real Banach space to `UCB G`. -/
def additiveLinearIsometryEquiv : AddUCB (Additive G) ≃ₗᵢ[ℝ] UCB G where
  toLinearEquiv := (additiveAlgEquiv G).toLinearEquiv
  norm_map' := norm_additiveAlgEquiv

@[simp]
theorem additiveLinearIsometryEquiv_apply (f : AddUCB (Additive G)) :
    additiveLinearIsometryEquiv G f = additiveAlgEquiv G f :=
  (rfl)

@[simp]
theorem additiveLinearIsometryEquiv_symm_apply (f : UCB G) :
    (additiveLinearIsometryEquiv G).symm f = (additiveAlgEquiv G).symm f :=
  (rfl)

@[simp]
theorem additiveAlgEquiv_leftTranslation (g : G) (f : AddUCB (Additive G)) :
    additiveAlgEquiv G (leftTranslation (ofMul g) f) =
      UCB.leftTranslation g (additiveAlgEquiv G f) := by
  ext
  simp

@[simp]
theorem additiveAlgEquiv_symm_leftTranslation (g : G) (f : UCB G) :
    (additiveAlgEquiv G).symm (UCB.leftTranslation g f) =
      leftTranslation (ofMul g) ((additiveAlgEquiv G).symm f) := by
  ext
  simp

@[simp]
theorem additiveAlgEquiv_rightTranslation (g : G) (f : AddUCB (Additive G)) :
    additiveAlgEquiv G (rightTranslation (ofMul g) f) =
      UCB.rightTranslation g (additiveAlgEquiv G f) := by
  ext
  simp

@[simp]
theorem additiveAlgEquiv_symm_rightTranslation (g : G) (f : UCB G) :
    (additiveAlgEquiv G).symm (UCB.rightTranslation g f) =
      rightTranslation (ofMul g) ((additiveAlgEquiv G).symm f) := by
  ext
  simp

/-- `additiveAlgEquiv` intertwines pullback along `φ.toAdditive` with pullback along `φ`. -/
theorem additiveAlgEquiv_compRightAlgHom (φ : G →ₜ* H) (f : AddUCB (Additive H)) :
    additiveAlgEquiv G (compRightAlgHom φ.toAdditive f) =
      UCB.compRightAlgHom φ (additiveAlgEquiv H f) := by
  ext
  simp

/-- `(additiveAlgEquiv _).symm` intertwines pullback along `φ` with pullback along
`φ.toAdditive`. -/
theorem additiveAlgEquiv_symm_compRightAlgHom (φ : G →ₜ* H) (f : UCB H) :
    (additiveAlgEquiv G).symm (UCB.compRightAlgHom φ f) =
      compRightAlgHom φ.toAdditive ((additiveAlgEquiv H).symm f) := by
  ext
  simp

end AddUCB

end Additive

end TauCeti
