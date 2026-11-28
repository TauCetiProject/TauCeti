/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.FDRep
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Flat.Basic
import TauCeti.LinearAlgebra.Determinant.FiniteOrder
import TauCeti.RepresentationTheory.CharacterTable.Degree.Basic
import TauCeti.RepresentationTheory.Charpoly
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Maschke
import TauCeti.RepresentationTheory.Simple.Basic
import TauCeti.RepresentationTheory.SplitRankTwo

/-!
# Vanishing of self-tensor Hom spaces in `FDRep`

Over an algebraically closed field, if a central element `g₀` of `G` has no eigenvalue `1` on `V`,
then `Hom_G(X, V ⊗ X) = 0` for every simple object `X : FDRep k G`
(`FDRep.finrank_hom_tensor_self_eq_zero_of_central_of_not_hasEigenvalue_one`).

In characteristic zero, every faithful two-dimensional representation `V` of determinant `1` of a
nontrivial finite group admits such a central element: an involution `-1` when `V` is simple, or an
arbitrary nontrivial element after splitting into two invariant lines when `V` is reducible.
Consequently `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`
(`FDRep.finrank_hom_tensor_self_eq_zero`), which is the loop-freeness of the McKay graph.

## Main results

* `FDRep.finrank_hom_tensor_self_eq_zero_of_central_of_not_hasEigenvalue_one`: vanishing of
  `dim_k Hom_G(X, V ⊗ X)` from a central element without eigenvalue `1` on `V`.
* `FDRep.finrank_hom_tensor_self_eq_zero`: loop-freeness for faithful two-dimensional
  representations of determinant `1` of a nontrivial finite group over an algebraically closed
  field of characteristic zero.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u v

namespace FDRep

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- Over an algebraically closed field, if a central group element `g₀` has no eigenvalue `1` on
`V`, then `dim_k Hom_G(X, V ⊗ X) = 0` for every simple object `X : FDRep k G`. -/
theorem finrank_hom_tensor_self_eq_zero_of_central_of_not_hasEigenvalue_one [IsAlgClosed k]
    {V : FDRep k G} {g₀ : G} (hcomm : ∀ h : G, g₀ * h = h * g₀)
    (hev : ¬ Module.End.HasEigenvalue (V.ρ g₀) 1) (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  have hX : _root_.Representation.IsIrreducible X.ρ := FDRep.isIrreducible_of_simple X
  obtain ⟨μ, hμ⟩ := hX.exists_forall_apply_eq_smul (X.ρ g₀) fun h x ↦ by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, hcomm h]
  have hμ0 : μ ≠ 0 := by
    have : Nontrivial X := hX.nontrivial
    obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
    rintro rfl
    apply hx₀
    calc x₀ = X.ρ (g₀⁻¹ * g₀) x₀ := by simp
      _ = X.ρ g₀⁻¹ (X.ρ g₀ x₀) := by rw [map_mul, mul_apply_eq_comp]
      _ = 0 := by rw [hμ x₀, zero_smul, map_zero]
  have htens : (V ⊗ X : FDRep k G).ρ g₀ = μ • (V.ρ g₀).rTensor X := by
    have hX_map : X.ρ g₀ = μ • LinearMap.id := by
      ext y
      simp [hμ y]
    rw [FDRep.tensor_ρ, hX_map]
    exact TensorProduct.ext' fun v y ↦ by simp [TensorProduct.tmul_smul]
  have hker : LinearMap.ker (V.ρ g₀ - 1) = ⊥ := by
    simpa [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def] using hev
  have hinj : Function.Injective ((V.ρ g₀ - 1).rTensor X) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := X) _ (LinearMap.ker_eq_bot.mp hker)
  have hf0 (f : X ⟶ V ⊗ X) : f = 0 := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun x ↦ ?_
    set z : V ⊗[k] X := f.hom.hom.hom x
    have heq : (V ⊗ X : FDRep k G).ρ g₀ z = μ • z := by
      simpa only [LinearMap.comp_apply, hμ x, map_smul] using
        (LinearMap.congr_fun (FDRep.hom_hom_hom_comm f g₀) x).symm
    rw [htens, LinearMap.smul_apply] at heq
    have hz : (V.ρ g₀).rTensor X z = z := smul_right_injective _ hμ0 heq
    have hz0 : ((V.ρ g₀ - 1).rTensor X) z = 0 := by simp [hz, Module.End.one_eq_id]
    rw [FDRep.zero_hom_hom_hom_apply]
    exact hinj (hz0.trans (map_zero _).symm)
  have : Subsingleton (X ⟶ V ⊗ X) := ⟨fun φ ψ ↦ (hf0 φ).trans (hf0 ψ).symm⟩
  exact Module.finrank_zero_of_subsingleton

/-- A reducible faithful semisimple two-dimensional representation of determinant `1` has a
central group element without eigenvalue `1`. -/
private theorem exists_central_no_eigenvalue_one_of_not_isIrreducible [Nontrivial G]
    {W₀ : Type*} [AddCommGroup W₀] [Module k W₀]
    {ρ : _root_.Representation k G W₀} [ρ.IsSemisimpleRepresentation]
    (hdim : Module.finrank k W₀ = 2)
    (hfaithful : Function.Injective ρ) (hdet : ∀ g : G, LinearMap.det (ρ g) = 1)
    (hρ : ¬ ρ.IsIrreducible) :
    ∃ g₀ : G, (∀ h : G, g₀ * h = h * g₀) ∧ ¬ Module.End.HasEigenvalue (ρ g₀) 1 := by
  -- Split `ρ` into two complementary invariant lines on which `G` acts by scalars.
  obtain ⟨W, W', hWW', hW1, hW'1⟩ :=
    _root_.Representation.exists_isCompl_finrank_eq_one_of_not_isIrreducible hdim hρ
  let e := _root_.Subrepresentation.equivProdOfIsCompl hWW'
  have he_apply (g : G) (v : W₀) := e.apply_eq_prod_det_smul_of_finrank_eq_one hW1 hW'1 g v
  have hdet_prod (g : G) :
      LinearMap.det (W.toRepresentation g) * LinearMap.det (W'.toRepresentation g) = 1 :=
    have : FiniteDimensional k W.toSubmodule := Module.finite_of_finrank_pos (by omega)
    have : FiniteDimensional k W'.toSubmodule := Module.finite_of_finrank_pos (by omega)
    ((e.det_apply_eq g).trans (LinearMap.det_prodMap _ _)).symm.trans (hdet g)
  have hcomm (g h : G) : g * h = h * g :=
    hfaithful <| LinearMap.ext fun v ↦ e.injective <| by
      simp [map_mul, mul_apply_eq_comp, he_apply, smul_smul, mul_comm]
  -- Any `g₀ ≠ 1` is central with diagonal eigenvalues `det (W g₀), det (W' g₀) ≠ 1`.
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : G)
  have hne_one :
      ¬ (LinearMap.det (W.toRepresentation g₀) = 1 ∧
          LinearMap.det (W'.toRepresentation g₀) = 1) := fun ⟨h1, h2⟩ ↦
    hg₀ <| hfaithful <| by
      rw [map_one]
      exact LinearMap.ext fun v ↦ e.injective (by simp [he_apply, h1, h2])
  have hc₁_ne : LinearMap.det (W.toRepresentation g₀) ≠ 1 := fun h1 ↦
    hne_one ⟨h1, by simpa [h1] using hdet_prod g₀⟩
  have hc₂_ne : LinearMap.det (W'.toRepresentation g₀) ≠ 1 := fun h2 ↦
    hne_one ⟨by simpa [h2] using hdet_prod g₀, h2⟩
  exact ⟨g₀, hcomm g₀, e.not_hasEigenvalue_of_prod_finrank_eq_one_of_det_ne hW1 hW'1 hc₁_ne hc₂_ne⟩

/-- **Loop-freeness of the McKay graph.** For a nontrivial finite group `G` and a faithful
two-dimensional representation `V : FDRep k G` of determinant `1` over an algebraically closed
field `k` of characteristic zero, `dim_k Hom_G(X, V ⊗ X) = 0` for every simple `X`. -/
theorem finrank_hom_tensor_self_eq_zero [IsAlgClosed k] [CharZero k] [Finite G] [Nontrivial G]
    (V : FDRep k G) (hdim : Module.finrank k V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) (X : FDRep k G) [Simple X] :
    Module.finrank k (X ⟶ V ⊗ X) = 0 := by
  by_cases hV : Simple V
  · have : _root_.Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' 2 (hdim ▸ FDRep.finrank_dvd_card V)
    have hg₀_ne : g₀ ≠ 1 := fun h1 ↦ by simp [h1] at hg₀
    have hg₀_sq : V.ρ g₀ * V.ρ g₀ = 1 := by
      rw [← map_mul, ← sq, ← hg₀, pow_orderOf_eq_one, map_one]
    have hVg₀ : V.ρ g₀ = -1 :=
      (LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one two_ne_zero hdim hg₀_sq
        (hdet g₀)).resolve_left fun h1 ↦ hg₀_ne (hfaithful (h1.trans (map_one V.ρ).symm))
    have hcomm (h : G) : g₀ * h = h * g₀ := hfaithful <| by
      rw [map_mul, map_mul, hVg₀, neg_one_mul, mul_neg_one]
    have hev : ¬ Module.End.HasEigenvalue (V.ρ g₀) 1 := by
      intro hev
      obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
      have hv_fix : V.ρ g₀ v = v := by simpa using Module.End.mem_eigenspace_iff.mp hv
      rw [hVg₀, LinearMap.neg_apply, Module.End.one_eq_id, LinearMap.id_apply,
        neg_eq_iff_add_eq_zero, ← two_smul k v] at hv_fix
      exact hv0 ((smul_eq_zero.mp hv_fix).resolve_left two_ne_zero)
    exact finrank_hom_tensor_self_eq_zero_of_central_of_not_hasEigenvalue_one hcomm hev X
  · have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    obtain ⟨g₀, hcomm, hev⟩ :=
      exists_central_no_eigenvalue_one_of_not_isIrreducible
        hdim hfaithful hdet (mt (FDRep.simple_iff_isIrreducible V).mpr hV)
    exact finrank_hom_tensor_self_eq_zero_of_central_of_not_hasEigenvalue_one hcomm hev X

end FDRep
