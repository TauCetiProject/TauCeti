/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Galois invariants of a scalar extension

For a Galois extension `L/k`, the elements of `L ⊗[k] A` fixed by the scalar-factor
action are precisely the tensors `1 ⊗ a`. This identifies the original vector space inside its
scalar extension, in arbitrary characteristic.

More generally, a subspace of `L ⊗[k] V` stable under the scalar-factor action is the scalar
extension of a unique subspace of `V`, namely of the vectors `v` with `1 ⊗ v` in it. The proof
reduces to the case of a stable subspace meeting the original space trivially, by passing to the
quotient; such a subspace is zero, because a nonzero element with fewest nonzero coordinates can be
normalized to be fixed. No finiteness of `L / k` or of `V` is required. Closed subgroups of an
affine group over `k` are recovered from their scalar extensions in this way.

An algebra morphism between scalar extensions
therefore descends uniquely if and only if it commutes with the scalar-factor Galois action.
This supplies the underlying algebra map for descent of coordinate bialgebra morphisms.

## Main declarations

* `TauCeti.GaloisDescent.tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq`: the fixed
  tensors are exactly those coming from the original vector space.
* `Submodule.baseChange_comap_eq_of_forall_map_mem`: a Galois-stable subspace of a scalar
  extension is the scalar extension of its intersection with the original space.
* `Submodule.existsUnique_baseChange_eq_iff_forall_map_mem`: the subspaces arising by scalar
  extension are exactly the Galois-stable ones, and each arises from a unique subspace.
* `AlgHom.galoisDescend`: descent of an equivariant algebra morphism.
* `AlgHom.existsUnique_map_eq_iff`: equivariance characterizes unique descent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §AG.14.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup A] [Module k A] [IsGalois k L]

/-- The fixed elements of a scalar extension along a Galois extension are exactly
the image of the original vector space. -/
theorem tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq (x : L ⊗[k] A) :
    (∀ σ : L ≃ₐ[k] L, TensorProduct.map σ.toLinearMap LinearMap.id x = x) ↔
      ∃ a : A, 1 ⊗ₜ[k] a = x := by
  classical
  let b := Module.Free.chooseBasis k A
  constructor
  · intro hx
    have hc (i) : ∃ c : k, algebraMap k L c = (b.baseChange L).repr x i := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      exact (b.map_baseChange_repr σ.toLinearMap x i).trans
        (congrArg (fun y ↦ (b.baseChange L).repr y i) (hx σ))
    choose c hc using hc
    refine ⟨∑ i ∈ ((b.baseChange L).repr x).support, c i • b i, ?_⟩
    conv_rhs => rw [← (b.baseChange L).linearCombination_repr x]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      Finsupp.linearCombination_apply, Finsupp.sum, Module.Basis.baseChange_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hc i]
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
  · rintro ⟨a, rfl⟩ σ
    simp

end TauCeti.GaloisDescent

namespace Submodule

open TauCeti.GaloisDescent

variable {k L V : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [IsGalois k L]

/-- A Galois-stable subspace of a scalar extension containing no nonzero tensor `1 ⊗ v` is zero. -/
private theorem eq_bot_of_forall_map_mem (W : Submodule L (L ⊗[k] V))
    (hW : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ W, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ W)
    (h : ∀ v : V, 1 ⊗ₜ[k] v ∈ W → v = 0) : W = ⊥ := by
  classical
  let c := (Module.Free.chooseBasis k V).baseChange L
  by_contra hne
  have hex : ∃ n, ∃ w ∈ W, w ≠ 0 ∧ (c.repr w).support.card = n := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨_, w, hw, hw0, rfl⟩
  -- Choose a nonzero element of `W` with the fewest nonzero coordinates.
  obtain ⟨w, hw, hw0, hcard⟩ := Nat.find_spec hex
  obtain ⟨i, hi⟩ : (c.repr w).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact (map_ne_zero_iff _ c.repr.injective).mpr hw0
  have hwi : c.repr w i ≠ 0 := Finsupp.mem_support_iff.mp hi
  -- Normalize its `i`-th coordinate to `1`.
  set u := (c.repr w i)⁻¹ • w
  have hu : u ∈ W := W.smul_mem _ hw
  have hui : c.repr u i = 1 := by simp [u, inv_mul_cancel₀ hwi]
  have hsupp : (c.repr u).support = (c.repr w).support := by
    simp only [u, map_smul]
    exact Finsupp.support_smul_eq (inv_ne_zero hwi)
  -- A Galois translate of `u` differs from `u` by an element of `W` of smaller support, so it
  -- agrees with `u`.
  have hfix (σ : L ≃ₐ[k] L) : TensorProduct.map σ.toLinearMap LinearMap.id u = u := by
    by_contra hne'
    set d := TensorProduct.map σ.toLinearMap LinearMap.id u - u
    have hrepr (j) : c.repr d j = σ (c.repr u j) - c.repr u j := by
      simp only [d, map_sub, Finsupp.sub_apply, c, AlgEquiv.toLinearMap_apply,
        ← (Module.Free.chooseBasis k V).map_baseChange_repr σ.toLinearMap]
    have hsub : (c.repr d).support ⊂ (c.repr u).support := by
      refine (Finset.ssubset_iff_of_subset fun j hj ↦ ?_).mpr ⟨i, by rwa [hsupp], ?_⟩
      · rw [Finsupp.mem_support_iff] at hj ⊢
        intro hu0
        exact hj (by rw [hrepr, hu0, map_zero, sub_zero])
      · rw [Finsupp.notMem_support_iff, hrepr, hui, map_one, sub_self]
    have hmin := Nat.find_min' hex ⟨d, W.sub_mem (hW σ u hu) hu, sub_ne_zero.mpr hne', rfl⟩
    have := Finset.card_lt_card hsub
    rw [hsupp] at this
    omega
  -- Hence `u` is a fixed tensor `1 ⊗ v`, which forces `u = 0`.
  obtain ⟨v, hv⟩ := (tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq u).mp hfix
  rw [h v (hv ▸ hu), TensorProduct.tmul_zero] at hv
  simp [← hv] at hui

/-- **Galois descent of subspaces.** Along a Galois extension `L / k`, a subspace of `L ⊗[k] V`
stable under the scalar-factor Galois action is the scalar extension of the subspace of `V`
consisting of the vectors `v` with `1 ⊗ v` in it. -/
theorem baseChange_comap_eq_of_forall_map_mem (W : Submodule L (L ⊗[k] V))
    (hW : ∀ σ : L ≃ₐ[k] L, ∀ x ∈ W, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ W) :
    ((W.restrictScalars k).comap (TensorProduct.mk k L V 1)).baseChange L = W := by
  set p := (W.restrictScalars k).comap (TensorProduct.mk k L V 1)
  have hle : p.baseChange L ≤ W := baseChange_le_iff_le_comap.mpr le_rfl
  refine le_antisymm hle fun x hx ↦ ?_
  -- Pass to `L ⊗[k] (V ⧸ p)`, whose kernel from `L ⊗[k] V` is `p.baseChange L` by right
  -- exactness, and where the image of `W` meets the original space trivially.
  let f : L ⊗[k] V →ₗ[L] L ⊗[k] (V ⧸ p) := TensorProduct.AlgebraTensorModule.lTensor L L p.mkQ
  have hf (y : L ⊗[k] V) : f y = p.mkQ.lTensor L y :=
    congrFun (TensorProduct.AlgebraTensorModule.coe_lTensor (A := L) (M := L) p.mkQ) y
  have hker {y : L ⊗[k] V} (hy : f y = 0) : y ∈ p.baseChange L := by
    rw [hf, ← LinearMap.mem_ker, lTensor_mkQ] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, rfl⟩
  have hcomm (σ : L ≃ₐ[k] L) (y : L ⊗[k] V) :
      TensorProduct.map σ.toLinearMap LinearMap.id (f y) =
        f (TensorProduct.map σ.toLinearMap LinearMap.id y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a v => simp [hf]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hbot : W.map f = ⊥ := by
    refine eq_bot_of_forall_map_mem _ ?_ ?_
    · rintro σ _ ⟨y, hy, rfl⟩
      exact ⟨_, hW σ y hy, (hcomm σ y).symm⟩
    · intro v ⟨y, hy, hyv⟩
      obtain ⟨v, rfl⟩ := p.mkQ_surjective v
      have hdiff : y - 1 ⊗ₜ[k] v ∈ W := hle (hker (by rw [map_sub, hyv]; simp [hf]))
      have hv : 1 ⊗ₜ[k] v ∈ W := by simpa using W.sub_mem hy hdiff
      exact (Submodule.Quotient.mk_eq_zero p).mpr hv
  have hfx : f x ∈ W.map f := ⟨x, hx, rfl⟩
  rw [hbot, Submodule.mem_bot] at hfx
  exact hker hfx

/-- Along a Galois extension `L / k`, a subspace of `L ⊗[k] V` is the scalar extension of a
subspace of `V` exactly when it is stable under the scalar-factor Galois action, and that subspace
of `V` is then unique. -/
theorem existsUnique_baseChange_eq_iff_forall_map_mem (W : Submodule L (L ⊗[k] V)) :
    (∃! p : Submodule k V, p.baseChange L = W) ↔
      ∀ σ : L ≃ₐ[k] L, ∀ x ∈ W, TensorProduct.map σ.toLinearMap LinearMap.id x ∈ W := by
  constructor
  · rintro ⟨p, rfl, -⟩ σ x hx
    exact p.map_mem_baseChange σ.toLinearMap hx
  · intro hW
    exact ⟨_, W.baseChange_comap_eq_of_forall_map_mem hW, fun p hp ↦
      baseChange_injective (hp.trans (W.baseChange_comap_eq_of_forall_map_mem hW).symm)⟩

end Submodule

namespace AlgHom

variable {k L A B : Type*} [Field k] [Field L] [Algebra k L]
variable [Semiring A] [Semiring B] [Algebra k A] [Algebra k B]
variable [IsGalois k L]

variable (F : L ⊗[k] A →ₐ[L] L ⊗[k] B)
variable (hF : ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
  F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
    TensorProduct.map σ.toLinearMap LinearMap.id (F x))

include hF in
private theorem galoisDescend_mem_range (a : A) :
    ((F.restrictScalars k).comp Algebra.TensorProduct.includeRight) a ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] L ⊗[k] B).range := by
  let := Module.addCommMonoidToAddCommGroup k (M := B)
  apply (TauCeti.GaloisDescent.tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq
    (F (1 ⊗ₜ[k] a))).mp
  intro σ
  simpa using (hF σ (1 ⊗ₜ[k] a)).symm

/-- Descent of an algebra morphism commuting with the scalar-factor Galois action.
Its scalar extension is the original morphism. -/
noncomputable def galoisDescend : A →ₐ[k] B := by
  letI := Module.addCommMonoidToAddCommGroup k (M := B)
  exact (AlgEquiv.ofInjective Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)).symm.toAlgHom.comp
      (((F.restrictScalars k).comp Algebra.TensorProduct.includeRight).codRestrict _
        (galoisDescend_mem_range F hF))

/-- The descended morphism is characterized on the original algebra inside its scalar extension. -/
@[simp]
theorem one_tmul_galoisDescend (a : A) :
    1 ⊗ₜ[k] F.galoisDescend hF a = F (1 ⊗ₜ[k] a) := by
  let := Module.addCommMonoidToAddCommGroup k (M := B)
  let e := AlgEquiv.ofInjective (Algebra.TensorProduct.includeRight : B →ₐ[k] L ⊗[k] B)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)
  let g := ((F.restrictScalars k).comp Algebra.TensorProduct.includeRight).codRestrict _
    (galoisDescend_mem_range F hF)
  have h := congrArg Subtype.val (e.apply_symm_apply (g a))
  simpa only [e, AlgEquiv.ofInjective_apply, Algebra.TensorProduct.includeRight_apply,
    g, AlgHom.coe_codRestrict, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    galoisDescend, AlgEquiv.coe_toAlgHom] using h

/-- Extending a descended algebra morphism recovers the given equivariant morphism. -/
@[simp]
theorem map_galoisDescend :
    Algebra.TensorProduct.map (AlgHom.id L L) (F.galoisDescend hF) = F := by
  apply Algebra.TensorProduct.ext'
  intro l a
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    TensorProduct.tmul_eq_smul_one_tmul l a, map_smul,
    ← one_tmul_galoisDescend F hF, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- An algebra morphism over a Galois extension descends uniquely exactly when it
commutes with the scalar-factor Galois action. -/
theorem existsUnique_map_eq_iff :
    (∃! f : A →ₐ[k] B, Algebra.TensorProduct.map (AlgHom.id L L) f = F) ↔
      ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
        F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
          TensorProduct.map σ.toLinearMap LinearMap.id (F x) := by
  constructor
  · rintro ⟨f, rfl, _⟩ σ x
    exact TauCeti.ScalarAut.baseChangeMap_smul f σ x
  · intro hF
    let := Module.addCommMonoidToAddCommGroup k (M := B)
    refine ⟨F.galoisDescend hF, F.map_galoisDescend hF, fun f hf ↦ ?_⟩
    ext a
    apply Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap k L).injective
    have h := DFunLike.congr_fun hf (1 ⊗ₜ[k] a)
    simpa using h.trans (F.one_tmul_galoisDescend hF a).symm

end AlgHom
