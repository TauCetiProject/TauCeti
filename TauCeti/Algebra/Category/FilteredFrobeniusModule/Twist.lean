/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FilteredFrobeniusModule.Basic

/-!
# Twists of filtered Frobenius modules

The *twist* `M(j)` of a filtered Frobenius module `M` by an integer `j` has the same underlying
module, the shifted filtration `Fil^i M(j) = Fil^(i - j) M` and the divided Frobenius maps
`φ^i_{M(j)} = φ^(i - j)_M`. It moves the filtration jumps up by `j`, so an object supported in
`[a, b]` becomes one supported in `[a + j, b + j]`; it is the filtered counterpart of a Tate
twist. Twisting by `j` does not change the morphisms, and it is an autoequivalence of the
category of filtered Frobenius modules with inverse the twist by `-j`.

## Main definitions

* `TauCeti.FilteredFrobeniusModule.twist M j`: the twist `M(j)`.
* `TauCeti.FilteredFrobeniusModule.twistFunctor j`: the twist as an endofunctor.
* `TauCeti.FilteredFrobeniusModule.twistFunctorZeroIso` and
  `TauCeti.FilteredFrobeniusModule.twistFunctorAddIso`: `M(0) ≅ M` and `M(j)(k) ≅ M(j + k)`,
  naturally in `M`.

## Main results

* `TauCeti.FilteredFrobeniusModule.isSupportedIn_twist_iff`: `M(j)` is supported in `[a, b]`
  iff `M` is supported in `[a - j, b - j]`.
* `TauCeti.FilteredFrobeniusModule.isGenerating_twist_iff`: `M(j)` is generating iff `M` is.
* The twist functor is an equivalence.

## References

* J.-M. Fontaine and G. Laffaille, *Construction de représentations p-adiques*, Ann. Sci. École
  Norm. Sup. (4) 15 (1982), §§3.2 and 5.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti.FilteredFrobeniusModule

variable {W : Type u} [CommRing W] {σ : W →+* W} {ϖ : W}

/-- The twist `M(j)` of a filtered Frobenius module: the same module with
`Fil^i M(j) = Fil^(i - j) M` and `φ^i_{M(j)} = φ^(i - j)_M`. -/
abbrev twist (M : FilteredFrobeniusModule.{v} σ ϖ) (j : ℤ) : FilteredFrobeniusModule.{v} σ ϖ where
  toModuleCat := M.toModuleCat
  fil i := M.fil (i - j)
  fil_antitone _ _ h := M.fil_antitone (by omega)
  iSup_fil := ((Equiv.subRight j).iSup_comp (g := M.fil)).trans M.iSup_fil
  iInf_fil := ((Equiv.subRight j).iInf_comp (g := M.fil)).trans M.iInf_fil
  phi i := M.phi (i - j)
  phi_succ i x hx := by
    have hx' : x ∈ M.fil (i - j + 1) := by rwa [sub_add_eq_add_sub]
    rw [M.phi_congr (sub_add_eq_add_sub i j 1).symm hx hx']
    exact M.phi_succ (i - j) x hx'

variable (M N : FilteredFrobeniusModule.{v} σ ϖ) (j k : ℤ)

@[simp]
theorem twist_toModuleCat : (M.twist j).toModuleCat = M.toModuleCat := (rfl)

@[simp]
theorem twist_fil (i : ℤ) : (M.twist j).fil i = M.fil (i - j) := (rfl)

@[simp]
theorem twist_phi (i : ℤ) (x : M) (hx : x ∈ (M.twist j).fil i) :
    (M.twist j).phi i ⟨x, hx⟩ = M.phi (i - j) ⟨x, hx⟩ := (rfl)

/-- `M(j)` is supported in `[a, b]` iff `M` is supported in `[a - j, b - j]`. -/
@[simp]
theorem isSupportedIn_twist_iff (a b : ℤ) :
    (M.twist j).IsSupportedIn a b ↔ M.IsSupportedIn (a - j) (b - j) := by
  simp only [isSupportedIn_iff, sub_add_eq_add_sub]

/-- `M(j)` is supported in `[a + j, b + j]` iff `M` is supported in `[a, b]`. -/
theorem isSupportedIn_twist_add_iff (a b : ℤ) :
    (M.twist j).IsSupportedIn (a + j) (b + j) ↔ M.IsSupportedIn a b := by
  simp [isSupportedIn_twist_iff]

/-- `M(j)` is generating iff `M` is. -/
@[simp]
theorem isGenerating_twist_iff : (M.twist j).IsGenerating ↔ M.IsGenerating := by
  simp only [isGenerating_iff]
  exact Iff.of_eq (congrArg (fun s => Submodule.span W s = ⊤)
    ((Equiv.subRight j).iSup_comp (g := fun i => Set.range (M.phi i))))

/-- The twist by `j` as an endofunctor: it does not change underlying linear maps. -/
@[expose]
def twistFunctor : FilteredFrobeniusModule.{v} σ ϖ ⥤ FilteredFrobeniusModule.{v} σ ϖ where
  obj M := M.twist j
  map f := ⟨f.hom, fun i => f.map_fil (i - j), fun i => f.hom_phi (i - j)⟩

@[simp]
theorem twistFunctor_obj : (twistFunctor j).obj M = M.twist j := (rfl)

@[simp]
theorem twistFunctor_map_hom {M N : FilteredFrobeniusModule.{v} σ ϖ} (f : M ⟶ N) :
    ((twistFunctor j).map f).hom = f.hom := (rfl)

/-- `M(0) ≅ M`, by the identity of the underlying module. -/
def twistZeroIso : M.twist 0 ≅ M :=
  isoMk (LinearEquiv.refl W M) (fun i => by simp) fun i _ _ => M.phi_congr (sub_zero i) _ _

/-- `M(j)(k) ≅ M(j + k)`, by the identity of the underlying module. -/
def twistTwistIso : (M.twist j).twist k ≅ M.twist (j + k) :=
  isoMk (LinearEquiv.refl W M) (fun i => by simp [sub_sub, add_comm k j])
    fun _ _ _ => M.phi_congr (by ring) _ _

@[simp]
theorem twistZeroIso_hom_hom : (M.twistZeroIso).hom.hom = LinearMap.id :=
  isoMk_hom_hom _ _ _

@[simp]
theorem twistZeroIso_inv_hom : (M.twistZeroIso).inv.hom = LinearMap.id :=
  isoMk_inv_hom _ _ _

@[simp]
theorem twistTwistIso_hom_hom : (M.twistTwistIso j k).hom.hom = LinearMap.id :=
  isoMk_hom_hom _ _ _

@[simp]
theorem twistTwistIso_inv_hom : (M.twistTwistIso j k).inv.hom = LinearMap.id :=
  isoMk_inv_hom _ _ _

/-- The twist by `0` is naturally isomorphic to the identity functor. -/
def twistFunctorZeroIso : twistFunctor (σ := σ) (ϖ := ϖ) 0 ≅ 𝟭 _ :=
  -- The twisted and untwisted modules share their underlying module, so after `simp` both sides
  -- are `LinearMap.id ∘ₗ f.hom` and `f.hom ∘ₗ LinearMap.id` at different types: equal by `rfl`.
  NatIso.ofComponents twistZeroIso fun _ => hom_ext (by simp; rfl)

/-- Twisting by `j` and then by `k` is naturally isomorphic to twisting by `j + k`. -/
def twistFunctorAddIso :
    twistFunctor (σ := σ) (ϖ := ϖ) j ⋙ twistFunctor k ≅ twistFunctor (j + k) :=
  -- The twisted and untwisted modules share their underlying module, so after `simp` both sides
  -- are `LinearMap.id ∘ₗ f.hom` and `f.hom ∘ₗ LinearMap.id` at different types: equal by `rfl`.
  NatIso.ofComponents (fun M => M.twistTwistIso j k) fun _ => hom_ext (by simp; rfl)

instance : (twistFunctor (σ := σ) (ϖ := ϖ) j).Faithful where
  map_injective {M N} _ _ h := hom_ext (congrArg (fun f : M.twist j ⟶ N.twist j => f.hom) h)

instance : (twistFunctor (σ := σ) (ϖ := ϖ) j).Full where
  map_surjective {M N} g := by
    -- The objects `(twistFunctor j).obj M` are `M.twist j` by definition.
    let g' : M.twist j ⟶ N.twist j := g
    refine ⟨⟨g'.hom, fun i x hx => ?_, fun i x hx => ?_⟩, rfl⟩
    · have hx' : x ∈ (M.twist j).fil (i + j) := by simpa using hx
      simpa using g'.map_fil (i + j) hx'
    · have hx' : x ∈ (M.twist j).fil (i + j) := by simpa using hx
      have := g'.hom_phi (i + j) x hx'
      rw [twist_phi, twist_phi] at this
      rw [M.phi_congr (add_sub_cancel_right i j).symm hx (by simpa using hx'), this,
        N.phi_congr (add_sub_cancel_right i j)]

instance : (twistFunctor (σ := σ) (ϖ := ϖ) j).EssSurj where
  mem_essImage M := ⟨M.twist (-j), ⟨M.twistTwistIso (-j) j ≪≫
    eqToIso (congrArg M.twist (neg_add_cancel j)) ≪≫ M.twistZeroIso⟩⟩

instance : (twistFunctor (σ := σ) (ϖ := ϖ) j).IsEquivalence where

end TauCeti.FilteredFrobeniusModule
