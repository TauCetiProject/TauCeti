/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.FractionRing
public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.RingTheory.KrullSchmidt.FractionRing

/-!
# The rational representation of a relation module

Let `R` be a domain with field of fractions `Q`, let `G` be a finite group whose order is nonzero
in `R`, and let `g : ι → G` be a generating family with `n + 1` members. The relation module of
`g` is the kernel of `R[G]^ι → I_G`, `e_i ↦ g_i - 1`, so it sits in Lyndon's exact sequence

`0 → relationModule R G g → R[G]^ι → I_G → 0`.

After tensoring with `Q` this sequence and the augmentation sequence `0 → I_G → R[G] → R → 0`
split (Maschke's theorem, `TauCeti.IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact`), and
cancelling the rational regular representation gives

`relationModule R G g ⊗ Q ≃ (R[G]^n ⊕ R) ⊗ Q`,

that is, the rationalized relation module is `Q[G]^n ⊕ Q`: `n` copies of the regular
representation and one trivial representation. Its rational representation depends only on the
number of generators, not on the group-theoretic relations among them.

For `R = ℤ_p` and `n + 1 = [K : ℚ_p] + 2` this is the rational shape of `R^ab(p)` for a finite
Galois layer of a `p`-adic field `K`. Comparing it with the rational decomposition of the
`p`-adic completion of the units of that layer computes the rational representation of the kernel
of a surjection between them, which is how that kernel is identified integrally in the proof of
NSW (7.4.2)(i).

## Main results

* `TauCeti.MonoidAlgebra.nonempty_relationModule_tensor_linearEquiv`: for a generating family of
  size `n + 1`, `relationModule R G g ⊗[R] Q ≃ (R[G]^n × R[G] ⧸ I_G) ⊗[R] Q` as `R[G]`-modules.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition, (5.6.6)
  and the proof of (7.4.2).
* W. Gaschütz, *Über modulare Darstellungen endlicher Gruppen, die von freien Gruppen induziert
  werden*, Math. Z. 60 (1954), 274–286.
-/

public section

open scoped TensorProduct

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

variable {R : Type*} [CommRing R] (Q : Type*) [Field Q] [Algebra R Q] [IsFractionRing R Q]
  {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]

local notation "Λ" => _root_.MonoidAlgebra R G

/-- **The rational representation of a relation module** (Gaschütz). Let `R` be a domain with
field of fractions `Q` and `G` a finite group whose order is nonzero in `R`. For a generating family
`g` of `G` with `n + 1` members, the rationalized relation module of `g` is
`R[G]`-linearly isomorphic to `(R[G]^n × R[G] ⧸ I_G) ⊗[R] Q`, that is, to `Q[G]^n ⊕ Q`. -/
theorem nonempty_relationModule_tensor_linearEquiv [NeZero (Nat.card G : R)] {g : ι → G}
    (hg : Subgroup.closure (Set.range g) = ⊤) {n : ℕ} (hι : Fintype.card ι = n + 1) :
    Nonempty ((relationModule R G g ⊗[R] Q) ≃ₗ[Λ]
      (((Fin n → Λ) × (Λ ⧸ RingHom.ker (augmentation R G))) ⊗[R] Q)) := by
  set I := RingHom.ker (augmentation R G)
  set c := Fintype.linearCombination Λ fun i ↦ single (g i) (1 : R) - 1
  -- Lyndon's sequence `0 → relationModule R G g → R[G]^ι → I_G → 0`.
  let c' : (ι → Λ) →ₗ[Λ] I := c.codRestrict I fun x ↦
    range_linearCombination_le_ker_augmentation g (LinearMap.mem_range_self c x)
  have hc' : Function.Exact (relationModule R G g).subtype c' := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, relationModule_def,
      LinearMap.ker_codRestrict]
  have hc'' : Function.Surjective c' := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
      range_linearCombination_eq_ker_augmentation hg, Submodule.comap_subtype_self]
  -- Rationally, `R[G]^ι ≃ relationModule R G g ⊕ I_G` and `R[G] ≃ I_G ⊕ R[G] ⧸ I_G`.
  obtain ⟨e₁⟩ := IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact Q hc'
    (Submodule.injective_subtype _) hc''
  obtain ⟨e₂⟩ := IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact Q
    (LinearMap.exact_subtype_mkQ I) (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
  -- Integrally, `R[G]^ι × R[G] ⧸ I_G ≃ (R[G]^n × R[G] ⧸ I_G) × R[G]`, splitting off one
  -- coordinate of `R[G]^ι`.
  let e₃ : ((ι → Λ) × (Λ ⧸ I)) ≃ₗ[Λ] ((Fin n → Λ) × (Λ ⧸ I)) × Λ :=
    ((LinearEquiv.funCongrLeft Λ Λ (Fintype.equivFinOfCardEq hι).symm ≪≫ₗ
      (Fin.consLinearEquiv Λ fun _ : Fin (n + 1) ↦ Λ).symm).prodCongr (.refl Λ _)) ≪≫ₗ
      LinearEquiv.prodAssoc Λ _ _ _ ≪≫ₗ LinearEquiv.prodComm Λ _ _
  -- So `(relationModule R G g × R[G]) ⊗ Q ≃ ((R[G]^n × R[G] ⧸ I_G) × R[G]) ⊗ Q`; cancel `R[G]`,
  -- which is finitely generated over `R`.
  exact IsFractionRing.nonempty_tensor_linearEquiv_of_prod_tensor_linearEquiv Q
    ⟨TensorProduct.prodLeft _ _ _ _ _ ≪≫ₗ
      (LinearEquiv.refl Λ _).prodCongr (e₂ ≪≫ₗ TensorProduct.prodLeft _ _ _ _ _) ≪≫ₗ
      (LinearEquiv.prodAssoc Λ _ _ _).symm ≪≫ₗ
      ((TensorProduct.prodLeft _ _ _ _ _).symm ≪≫ₗ e₁.symm).prodCongr (.refl Λ _) ≪≫ₗ
      (TensorProduct.prodLeft _ _ _ _ _).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr e₃ (.refl R Q)⟩

end TauCeti.MonoidAlgebra
