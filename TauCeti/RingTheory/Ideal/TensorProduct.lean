/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.Algebra.Module.Submodule.LinearMap
public import TauCeti.LinearAlgebra.TensorProduct.Kernel
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.LinearAlgebra.TensorProduct.Torsion
public import Mathlib.LinearAlgebra.Dimension.Finrank

import TauCeti.RingTheory.Ideal.Operations

/-!
# Extended ideals and annihilators under scalar extension

The scalar multiplication equivalence `S ⊗[R] R ≃ₗ[S] S` identifies the base change of
an ideal with its extension along `algebraMap R S`. This permits kernel computations
on tensor products to be read as membership statements in extended ideals.
The extension of a module annihilator is contained in its annihilator after arbitrary
scalar extension, without a flatness hypothesis. The coefficient algebra `S` need not be
commutative; extended ideals are left ideals.

For an ideal `I` and a module `M`, injectivity of `I ⊗ M → R ⊗ M` is the vanishing of
`Tor₁(R ⧸ I, M)`. `Ideal.sup_subtype_rTensor_injective` propagates it from `I` and `J` to `I ⊔ J`,
provided `I M ∩ J M = (I ⊓ J) M`.

Along a flat ring map `R → S` the base change `S ⊗[R] I` is the extended ideal `I S`, so the
fibres of `I` and `I S` at a field-valued point of `S` have the same dimension
(`Ideal.finrank_tensor_map_of_flat`). Without flatness, over a commutative `S`, the map
`S ⊗[R] I → I S` is still surjective (`Ideal.liftBaseChange_idealMap_surjective`) and its kernel
is killed by `I S` (`Ideal.isTorsionBySet_ker_liftBaseChange_idealMap`). For an idempotent ideal
`I`, `I S • (S ⊗[R] I) = S ⊗[R] I` (`Ideal.smul_top_baseChange_eq_top`), and it follows that
`S ⊗[R] (I ⊗[R] I) ≅ I S ⊗[S] I S` (`Ideal.baseChangeTensorSelfEquiv`), which is how basic
setups of almost mathematics base change (Gabber–Ramero, *Almost ring theory*, Remark 2.1.4(ii)).
-/

public section

open TensorProduct
open scoped Pointwise

namespace Ideal

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- The extended ideal is the image of its tensor base change under scalar multiplication. -/
theorem map_eq_baseChange_map_rid (I : Ideal R) :
    I.map (algebraMap R S) =
      (I.baseChange S).map (AlgebraTensorModule.rid R S S).toLinearMap := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
    Set.image_image]
  simp only [LinearEquiv.coe_coe, TensorProduct.mk_apply,
    AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
  rfl

end Ideal

namespace LinearMap

variable {R S M : Type*} [CommRing R] [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Flatness tests membership in an extended scalar-source kernel on `s ⊗ₜ 1`. -/
theorem mem_map_ker_iff_of_flat [Module.Flat R S] (f : R →ₗ[R] M) (s : S) :
    s ∈ Ideal.map (algebraMap R S) (ker f) ↔ f.baseChange S (s ⊗ₜ[R] 1) = 0 := by
  rw [Ideal.map_eq_baseChange_map_rid, ← f.ker_baseChange_of_flat S,
    Submodule.mem_map_equiv, AlgebraTensorModule.rid_symm_apply, mem_ker]

end LinearMap

namespace TauCeti

section Semiring

variable {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Extension of the annihilator is contained in the annihilator after arbitrary base change. -/
theorem annihilator_map_le_baseChange :
    (Module.annihilator R M).map (algebraMap R S) ≤
      Module.annihilator S (S ⊗[R] M) := by
  refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ Module.mem_annihilator.mpr fun x ↦ ?_
  have h := isTorsionBy_tensorProduct_right (R := R) (M := S) (S := R)
    ((Module.isTorsionBy_iff_mem_annihilator R M).mpr hr)
  simpa only [algebraMap_smul] using h (x := x)

end Semiring

end TauCeti

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `I ⊗ M → R ⊗ M` and `J ⊗ M → R ⊗ M` are injective, that is, if
`Tor₁(R ⧸ I, M) = Tor₁(R ⧸ J, M) = 0`, and `I M ∩ J M = (I ⊓ J) M`, then `(I ⊔ J) ⊗ M → R ⊗ M` is
injective as well. -/
theorem sup_subtype_rTensor_injective {I J : Ideal R}
    (hI : Function.Injective (I.subtype.rTensor M))
    (hJ : Function.Injective (J.subtype.rTensor M))
    (hIJ : I • (⊤ : Submodule R M) ⊓ J • ⊤ ≤ (I ⊓ J) • ⊤) :
    Function.Injective ((I ⊔ J).subtype.rTensor M) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨a, b, rfl⟩ := Submodule.exists_eq_rTensor_inclusion_add I J t
  simp only [map_add, ← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion] at ht
  -- The image of `a` in `M` lies in `I M ∩ J M`, hence comes from some `s : (I ⊓ J) ⊗ M`.
  obtain ⟨s, hs⟩ : TensorProduct.lid R M (I.subtype.rTensor M a) ∈
      LinearMap.range ((TensorProduct.lid R M).comp ((I ⊓ J).subtype.rTensor M)) := by
    rw [subtype_rTensor_range]
    refine hIJ ⟨?_, ?_⟩
    · rw [← subtype_rTensor_range]
      exact ⟨a, rfl⟩
    · rw [eq_neg_of_add_eq_zero_left ht, map_neg, ← subtype_rTensor_range]
      exact neg_mem ⟨b, rfl⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, (TensorProduct.lid R M).injective.eq_iff] at hs
  -- Since `I ⊗ M → R ⊗ M` and `J ⊗ M → R ⊗ M` are injective, `a` and `-b` both come from `s`.
  have ha : (Submodule.inclusion inf_le_left).rTensor M s = a := hI (by
    rw [← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion, hs])
  have hb : (Submodule.inclusion inf_le_right).rTensor M (-s) = b := hJ (by
    rw [← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion, map_neg, hs,
      eq_neg_of_add_eq_zero_right ht])
  simp only [← ha, ← hb, ← LinearMap.rTensor_comp_apply, Submodule.inclusion_comp_inclusion,
    map_neg, add_neg_cancel]

end Ideal

namespace Ideal

variable {R S F : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field F] [Algebra R F]
  [Algebra S F] [IsScalarTower R S F]

/-- Along a flat ring map `R → S`, the fibre of the extended ideal `I S` at a field-valued point
`S → F` has the same dimension as the fibre of `I`: by flatness, `S ⊗[R] I` is `I S`. The
identification `S ⊗[R] I ≃ I S` follows the construction in the proof of Mathlib's
`Ideal.FG.of_FG_map_of_faithfullyFlat`. -/
theorem finrank_tensor_map_of_flat [Module.Flat R S] (I : Ideal R) :
    Module.finrank F (F ⊗[S] I.map (algebraMap R S)) = Module.finrank F (F ⊗[R] I) := by
  let f : S ⊗[R] I →ₗ[S] S := (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ I.subtype.baseChange S
  have hf : Function.Injective f := (AlgebraTensorModule.rid R S S).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype)
  have hrange : LinearMap.range f = I.map (algebraMap R S) := by
    rw [map_eq_baseChange_map_rid, LinearMap.range_comp, Submodule.baseChange]
  let e : S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
    LinearEquiv.ofInjective f hf ≪≫ₗ LinearEquiv.ofEq _ _ hrange
  rw [← (e.baseChange S F _ _).finrank_eq,
    (AlgebraTensorModule.cancelBaseChange R S F F I).finrank_eq]

end Ideal

namespace Ideal

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] (I : Ideal R)

/-- The map `S ⊗[R] I → I S` induced by `I → I S` is surjective. -/
theorem liftBaseChange_idealMap_surjective :
    Function.Surjective ((Algebra.idealMap S I).liftBaseChange S) := by
  let J := I.map (algebraMap R S)
  have hle : J ≤ (LinearMap.range ((Algebra.idealMap S I).liftBaseChange S)).map J.subtype :=
    map_le_iff_le_comap.mpr fun a ha ↦
      ⟨⟨algebraMap R S a, mem_map_of_mem _ ha⟩, ⟨1 ⊗ₜ ⟨a, ha⟩, by ext; simp⟩, rfl⟩
  intro y
  obtain ⟨z, hz, hzy⟩ := hle y.2
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, Subtype.ext hzy⟩

/-- The kernel of the surjection `S ⊗[R] I → I S` is killed by the extended ideal `I S`. -/
theorem isTorsionBySet_ker_liftBaseChange_idealMap :
    Module.IsTorsionBySet S (LinearMap.ker ((Algebra.idealMap S I).liftBaseChange S))
      (I.map (algebraMap R S)) := by
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
    map_le_iff_le_comap]
  intro ε hε
  rw [mem_comap, Module.mem_annihilator]
  rintro ⟨k, hk⟩
  -- `s ⊗ a ↦ s ⊗ (a ε) = (ε s) ⊗ a` factors multiplication by `ε` through `S ⊗[R] I → I S`.
  have key : ∀ x : S ⊗[R] I, ((Algebra.idealMap S I).liftBaseChange S x : S) •
      (1 ⊗ₜ[R] ⟨ε, hε⟩) = algebraMap R S ε • x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul w a =>
      simp only [LinearMap.liftBaseChange_tmul, SetLike.val_smul, Algebra.idealMap_apply_coe,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [mul_comm, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul,
        TensorProduct.smul_tmul]
      congr 1
      ext; simp [mul_comm]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, add_smul, hx, hy, smul_add]
  apply Subtype.ext
  rw [Submodule.coe_smul, ← key, LinearMap.mem_ker.mp hk, Submodule.coe_zero, zero_smul,
    Submodule.coe_zero]

variable {I}

/-- For an idempotent ideal `I`, `I S • (S ⊗[R] I) = S ⊗[R] I`. -/
theorem smul_top_baseChange_eq_top (hI : IsIdempotentElem I) :
    I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] I)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul w a =>
    have ha : a ∈ I • (⊤ : Submodule R I) := by
      rw [smul_top_eq_top_of_isIdempotentElem hI]; exact Submodule.mem_top
    refine Submodule.smul_induction_on (p := fun a ↦ w ⊗ₜ[R] a ∈ _) ha (fun r hr y _ ↦ ?_)
      fun _ _ h₁ h₂ ↦ by rw [TensorProduct.tmul_add]; exact add_mem h₁ h₂
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  | add x y hx hy => exact add_mem hx hy

end Ideal

namespace Ideal

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}

/-- For an idempotent ideal `I`, the square `π ⊗ π` of `π : S ⊗[R] I → I S` is bijective: its
kernel is generated by `ker π ⊗ (S ⊗[R] I)` and `(S ⊗[R] I) ⊗ ker π`, which vanish since `I S`
kills `ker π` and `I S • (S ⊗[R] I) = S ⊗[R] I`. -/
private theorem map_liftBaseChange_idealMap_bijective (hI : IsIdempotentElem I) :
    Function.Bijective (TensorProduct.map ((Algebra.idealMap S I).liftBaseChange S)
      ((Algebra.idealMap S I).liftBaseChange S)) := by
  set π := (Algebra.idealMap S I).liftBaseChange S
  have hπ : Function.Surjective π := liftBaseChange_idealMap_surjective S I
  have hex := LinearMap.exact_subtype_ker_map π
  refine ⟨?_, TensorProduct.map_surjective hπ hπ⟩
  have := TauCeti.subsingleton_tensorProduct_of_isTorsionBySet_right
    (smul_top_baseChange_eq_top S hI) (isTorsionBySet_ker_liftBaseChange_idealMap S I)
  have := TauCeti.subsingleton_tensorProduct_of_isTorsionBySet_left
    (isTorsionBySet_ker_liftBaseChange_idealMap S I) (smul_top_baseChange_eq_top S hI)
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  have hx : x ∈ LinearMap.ker (TensorProduct.map π π) := hx
  -- The kernel types are given explicitly so that both exactness hypotheses unify.
  rw [TensorProduct.map_ker (M := LinearMap.ker π) (M' := LinearMap.ker π) hex hπ hex hπ] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  rw [Subsingleton.elim y 0, Subsingleton.elim z 0, map_zero, map_zero, add_zero]

/-- For an idempotent ideal `I`, the base change of `I ⊗[R] I` is the tensor square of the
extended ideal: `S ⊗[R] (I ⊗[R] I) ≅ I S ⊗[S] I S` (Gabber–Ramero Remark 2.1.4(ii)). -/
noncomputable def baseChangeTensorSelfEquiv (hI : IsIdempotentElem I) :
    S ⊗[R] (I ⊗[R] I) ≃ₗ[S] I.map (algebraMap R S) ⊗[S] I.map (algebraMap R S) :=
  AlgebraTensorModule.distribBaseChange R S I I ≪≫ₗ
    LinearEquiv.ofBijective _ (map_liftBaseChange_idealMap_bijective S hI)

@[simp]
theorem baseChangeTensorSelfEquiv_tmul (hI : IsIdempotentElem I) (s : S) (a b : I) :
    baseChangeTensorSelfEquiv S hI (s ⊗ₜ (a ⊗ₜ b)) =
      s • (Algebra.idealMap S I a ⊗ₜ[S] Algebra.idealMap S I b) := by
  simp [baseChangeTensorSelfEquiv, TensorProduct.smul_tmul']

end Ideal
