/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Kernels after extension of scalars

Mathlib's `Submodule.baseChange` extends a submodule of `M` to an `A`-submodule of `A ⊗[R] M`,
and `LinearMap.baseChange` extends a linear map.  For a general map the two constructions satisfy
only the containment `(ker f).baseChange A ≤ ker (f.baseChange A)`; it is an equality when `A` is
flat over `R`. This file records that case and two cases in which it is an equality for an
arbitrary coefficient algebra, flat or not: the kernel of a *surjective* map, and more generally
the kernel of a map whose cokernel `N ⧸ range f` is flat.

The first is the form wanted when the map is a quotient map, where the kernel of the extension is
to be identified with the extension of the submodule quotiented by. The second is the form wanted
for a kernel that should commute with every base change, such as the ring of invariants
`B^G = ker (b ↦ (g • b - b)_g)` of a finite group acting on an algebra `B` over a Dedekind domain,
where flatness of the cokernel is its torsion-freeness.

## Main results

* `LinearMap.ker_baseChange_of_flat`: over a flat coefficient algebra, the kernel of an extended
  linear map is the extension of its kernel.
* `LinearMap.ker_baseChange_of_surjective`: **for a surjective map the kernel of an extended
  linear map is the extension of its kernel**, with no hypothesis on the coefficient algebra.
* `LinearMap.ker_baseChange_of_flat_quotient_range`: the same for a map with flat cokernel.
* `LinearMap.finite_tensorProduct_ker`: over a flat coefficient algebra, the scalar extension of
  the kernel of a surjection is finite if the extended source is finite and the extended target is
  finitely presented.
* `Ideal.exists_smul_eq_of_rTensor_subtype_span_pair_injective`: if `I = Ideal.span {x, y}` has
  only Koszul relations and `I ⊗[R] B → R ⊗[R] B` is injective, then `x • b₁ = y • b₂` in `B`
  forces a common witness `b : B` with `y • b = b₁` and `x • b = b₂`.

## References

* [N. Bourbaki, *Algebra I, Chapters 1-3*][bourbaki1989], Chapter II, §3, n°6, for the exactness
  properties of the tensor product.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LinearMap

universe u v w x

variable {R : Type u} (A : Type v) {M : Type w} {N : Type x}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Ring A] [Algebra R A]

/-- Over a flat coefficient algebra, extension of scalars commutes with kernels. -/
theorem ker_baseChange_of_flat [Module.Flat R A] (f : M →ₗ[R] N) :
    ker (f.baseChange A) = (ker f).baseChange A := by
  have h : Function.Exact ((ker f).subtype.baseChange A) (f.baseChange A) := by
    simpa only [baseChange_eq_lTensor] using
      Module.Flat.lTensor_exact A f.exact_subtype_ker_map
  exact h.linearMap_ker_eq

/-- **Extension of scalars commutes with the kernel of a surjective map**, with no hypothesis on
the coefficient algebra.  Dropping surjectivity, the same equality holds when `A` is flat over
`R`, which is `LinearMap.ker_baseChange_of_flat`. -/
theorem ker_baseChange_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ker (f.baseChange A) = (ker f).baseChange A :=
  have h : Function.Exact ((ker f).subtype.baseChange A) (f.baseChange A) :=
    lTensor_exact A f.exact_subtype_ker_map hf
  h.linearMap_ker_eq

/-- **Extension of scalars commutes with the kernel of a map with flat cokernel**, with no
hypothesis on the coefficient algebra. This generalizes `LinearMap.ker_baseChange_of_surjective`,
the case of zero cokernel. Over a Dedekind domain, for instance a principal ideal domain, a module
is flat if and only if it is torsion-free, so the hypothesis is then that `N ⧸ range f` is
torsion-free. -/
theorem ker_baseChange_of_flat_quotient_range (f : M →ₗ[R] N) [Module.Flat R (N ⧸ range f)] :
    ker (f.baseChange A) = (ker f).baseChange A := by
  -- `f` factors as the surjection `M → range f` followed by the inclusion `range f → N`, which
  -- stays injective after extending scalars because its cokernel is flat.
  have hinj : Function.Injective ((range f).subtype.baseChange A) := by
    rw [baseChange_eq_lTensor]
    exact lTensor_injective_of_exact_of_flat _ (range f).mkQ_surjective _
      (range f).injective_subtype (exact_subtype_mkQ _) A
  rw [← f.subtype_comp_rangeRestrict, baseChange_comp, ker_comp_of_ker_eq_bot _ (ker_eq_bot.2 hinj),
    ker_baseChange_of_surjective A _ f.surjective_rangeRestrict, ker_comp_of_ker_eq_bot _
      (range f).ker_subtype]

/-- For a flat scalar extension, the extended kernel of a surjection is finite whenever the
extended source is finite and the extended target is finitely presented. -/
theorem finite_tensorProduct_ker {S : Type*} [Ring S] [Algebra R S] [Module.Flat R S]
    [Module.Finite S (S ⊗[R] M)] [Module.FinitePresentation S (S ⊗[R] N)]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite S (S ⊗[R] ker f) := by
  have hfg := Module.FinitePresentation.fg_ker (f.baseChange S) (f.baseChange_surjective S hf)
  rw [ker_baseChange_of_flat] at hfg
  have : Module.Finite S ((ker f).baseChange S) := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.equiv (Submodule.toBaseChange.toLinearEquiv S (ker f)).symm

end LinearMap

namespace Ideal

/-- **Two-generator Koszul `Tor₁` criterion.** If every relation `u * x + v * y = 0` in `R` is a
multiple of `(y, -x)` and `(Ideal.span {x, y}).subtype.rTensor B` is injective, then every relation
`x • b₁ = y • b₂` in `B` comes from a common element `b : B` with `y • b = b₁` and `x • b = b₂`. -/
theorem exists_smul_eq_of_rTensor_subtype_span_pair_injective {R : Type*} [CommRing R]
    {B : Type*} [AddCommGroup B] [Module R B] {x y : R}
    (hkoszul : ∀ u v : R, u * x + v * y = 0 → ∃ a : R, u = a * y ∧ v = -(a * x))
    (hinj : Function.Injective ((Ideal.span ({x, y} : Set R)).subtype.rTensor B))
    {b₁ b₂ : B} (hrel : x • b₁ = y • b₂) :
    ∃ b : B, y • b = b₁ ∧ x • b = b₂ := by
  set I : Ideal R := Ideal.span ({x, y} : Set R)
  let φ : (R × R) →ₗ[R] I :=
    { toFun p := ⟨p.1 * x + p.2 * y, Ideal.mem_span_pair.mpr ⟨p.1, p.2, rfl⟩⟩
      map_add' _ _ := Subtype.ext (by
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]; ring)
      map_smul' _ _ := Subtype.ext (by
        simp only [RingHom.id_apply, SetLike.val_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring) }
  have hφ_surj : Function.Surjective φ := fun ⟨_, hr⟩ ↦
    let ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hr; ⟨(u, v), Subtype.ext huv⟩
  let κ : R →ₗ[R] R × R := (LinearMap.mulRight R y).prod (-LinearMap.mulRight R x)
  have hex : Function.Exact κ φ := fun p ↦ by
    refine ⟨fun hp ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
    · obtain ⟨a, hu, hv⟩ := hkoszul p.1 p.2 (congrArg Subtype.val hp)
      exact ⟨a, Prod.ext hu.symm hv.symm⟩
    · subst ha
      refine Subtype.ext ?_
      simp only [φ, κ, LinearMap.prod_apply, Function.prod_apply, LinearMap.mulRight_apply,
        LinearMap.neg_apply, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero]
      ring
  let w : (R × R) ⊗[R] B := (1, 0) ⊗ₜ[R] b₁ - (0, 1) ⊗ₜ[R] b₂
  have hw_ker : φ.rTensor B w = 0 := hinj <| by
    have hx₁ : x ⊗ₜ[R] b₁ = (1 : R) ⊗ₜ[R] (x • b₁) := by rw [← smul_tmul, smul_eq_mul, mul_one]
    have hy₂ : y ⊗ₜ[R] b₂ = (1 : R) ⊗ₜ[R] (y • b₂) := by rw [← smul_tmul, smul_eq_mul, mul_one]
    simp only [w, map_sub, LinearMap.rTensor_tmul, Submodule.coe_subtype, φ, LinearMap.coe_mk,
      AddHom.coe_mk, one_mul, zero_mul, add_zero, zero_add, map_zero, hx₁, hy₂, hrel, sub_self]
  obtain ⟨t, ht⟩ := (_root_.rTensor_exact B hex hφ_surj w).mp hw_ker
  have ht' : t = (1 : R) ⊗ₜ[R] TensorProduct.lid R B t := by
    rw [← lid_symm_apply, LinearEquiv.symm_apply_apply]
  refine ⟨TensorProduct.lid R B t, ?_, ?_⟩
  · have h₁ := congrArg ((TensorProduct.lid R B).toLinearMap ∘ₗ
      (LinearMap.fst R R R).rTensor B) ht
    conv_lhs at h₁ => rw [ht']
    simpa [w, κ] using h₁
  · have h₂ := congrArg ((TensorProduct.lid R B).toLinearMap ∘ₗ
      (LinearMap.snd R R R).rTensor B) ht
    conv_lhs at h₂ => rw [ht']
    exact neg_inj.mp (by simpa [w, κ] using h₂)

end Ideal
