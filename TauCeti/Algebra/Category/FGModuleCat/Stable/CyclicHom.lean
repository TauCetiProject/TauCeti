/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Cyclic
public import TauCeti.Algebra.Category.FGModuleCat.Stable.Basic
public import TauCeti.RingTheory.Noetherian.MulOpposite

/-!
# Stable morphisms between cyclic modules

Let `A` be an algebra over a field `k` and let `a, b : A`. A map of right `A`-modules out of the
cyclic module `A ⧸ aA` is determined by the image `m` of the generator, which can be any element
with `m * a = 0`. Such a map `A ⧸ aA ⟶ A ⧸ bA` factors through a projective module exactly when
it lifts along the quotient map `A ⟶ A ⧸ bA`, that is, when `m` is the class of an element of the
left annihilator of `a`. This gives the dimension of the stable morphism space as the difference

`dim {m ∈ A ⧸ bA | m * a = 0} - dim (image in A ⧸ bA of {c ∈ A | c * a = 0})`.

For the truncated polynomial algebra `A = K[X]/(X ^ n)` over a field `K`, with `x` the class of
`X` and `M_i = A ⧸ (x ^ i)`, both terms are explicit: the first is `min i j` and the second is
`j - min j (n - i)` (`TauCeti.FGModuleCat.finrank_cyclicModule_hom_root_pow`,
`TauCeti.FGModuleCat.finrank_map_ker_smul_op_root_pow`). Hence for `i, j ≤ n`

`dim_K Hom_stable(M_i, M_j) = min (min i j) (min (n - i) (n - j))`.

In particular `M_n = A` has no nonzero stable endomorphisms, and the stable dimensions are
unchanged when `(i, j)` is replaced by `(n - i, n - j)`, as they must be since the syzygy
autoequivalence sends `M_i` to `M_(n - i)`
(`TauCeti.FGModuleCat.stableModuleLoopCyclicModuleRootPowIso`). No hypothesis on the
characteristic of `K` is used.

Right `A`-modules are left `Aᵐᵒᵖ`-modules, so the condition `m * a = 0` is written `op a • m = 0`.
The description of maps out of `A ⧸ aA` by the image of the generator is
`TauCeti.FGModuleCat.cyclicModuleHomEquiv`. The `k`-vector space structure on morphisms is
Mathlib's `ModuleCat.linearOverField`, inherited by the stable category as a quotient by a
morphism ideal.

## Main results

* `TauCeti.FGModuleCat.stableModuleFunctor_map_cyclicModule_eq_zero_iff`: a map
  `A ⧸ aA ⟶ A ⧸ bA` vanishes in the stable module category exactly when the image of the
  generator is the class of an element `c` with `op a * c = 0`.
* `TauCeti.FGModuleCat.finrank_stableModuleHom_cyclicModule_add_finrank`: the dimension count for
  stable morphisms between cyclic modules.
* `TauCeti.FGModuleCat.finrank_stableModuleHom_cyclicModule_root_pow`: over `K[X]/(X ^ n)`, the
  dimension of the space of stable morphisms `M_i ⟶ M_j`.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2: the stable category of a Frobenius category.
-/

public section

namespace TauCeti

open CategoryTheory MulOpposite Module

universe w u

namespace FGModuleCat

variable {A : Type u} [Ring A]

/-! ### Stable morphisms between cyclic modules -/

section Stable

variable [IsNoetherianRing Aᵐᵒᵖ]

/-- A map `A ⧸ aA ⟶ A ⧸ bA` vanishes in the stable module category exactly when the image of the
generator is the class of an element `c` with `op a * c = 0`: the map then lifts along the
quotient map `A ⟶ A ⧸ bA`, which is an epimorphism from a projective module. -/
theorem stableModuleFunctor_map_cyclicModule_eq_zero_iff {a b : A}
    (f : cyclicModule a ⟶ cyclicModule b) :
    (stableModuleFunctor A).map f = 0 ↔
      ∃ c : Aᵐᵒᵖ, op a * c = 0 ∧
        Submodule.Quotient.mk c = f.hom.hom (Submodule.Quotient.mk 1) := by
  have : Projective (FGModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ) := _root_.FGModuleCat.projective_of_free Aᵐᵒᵖ _
  have : Epi (FGModuleCat.ofHom (Ideal.span {op b}).mkQ) :=
    ConcreteCategory.epi_of_surjective _ (Submodule.mkQ_surjective _)
  rw [stableModuleFunctor_map_eq_zero_iff_exists_lift (FGModuleCat.ofHom (Ideal.span {op b}).mkQ)]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.hom.hom (Submodule.Quotient.mk 1), smul_cyclicModule_hom_mk_one_eq_zero g, rfl⟩
  · rintro ⟨c, hc, hcf⟩
    refine ⟨cyclicModuleLift a c hc, cyclicModule_hom_ext ?_⟩
    rw [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, cyclicModuleLift_mk, one_smul,
      FGModuleCat.hom_hom_ofHom, Submodule.mkQ_apply, hcf]

variable (k : Type w) [Field k] [Algebra k A] [FiniteDimensional k A]

/-- **Dimension of stable morphisms between cyclic modules.** The stable morphisms
`A ⧸ aA ⟶ A ⧸ bA` together with the image in `A ⧸ bA` of the left annihilator of `a` have the
dimension of the space of elements of `A ⧸ bA` killed by `a`, which is the dimension of all
morphisms `A ⧸ aA ⟶ A ⧸ bA`. -/
theorem finrank_stableModuleHom_cyclicModule_add_finrank (a b : A) :
    finrank k ((stableModuleFunctor A).obj (cyclicModule a) ⟶
        (stableModuleFunctor A).obj (cyclicModule b)) +
      finrank k ((LinearMap.ker (DistribSMul.toLinearMap k Aᵐᵒᵖ (op a))).map
        ((Ideal.span {op b}).mkQ.restrictScalars k)) =
    finrank k (LinearMap.ker (DistribSMul.toLinearMap k (Aᵐᵒᵖ ⧸ Ideal.span {op b}) (op a))) := by
  let F := stableModuleFunctor A
  let e := cyclicModuleHomEquiv k a (M := Aᵐᵒᵖ ⧸ Ideal.span {op b})
  -- Evaluation at the generator embeds the morphisms into `A ⧸ bA`.
  let ev :=
    (LinearMap.ker (DistribSMul.toLinearMap k (Aᵐᵒᵖ ⧸ Ideal.span {op b}) (op a))).subtype ∘ₗ
      e.toLinearMap
  have hev : Function.Injective ev := Subtype.val_injective.comp e.injective
  have hev_apply (f : cyclicModule a ⟶ cyclicModule b) :
      ev f = f.hom.hom (Submodule.Quotient.mk 1) :=
    cyclicModuleHomEquiv_apply_coe k a f
  -- It identifies the stably trivial morphisms with the image of the annihilator of `a`.
  have hker : (LinearMap.ker (F.mapLinearMap k)).map ev =
      (LinearMap.ker (DistribSMul.toLinearMap k Aᵐᵒᵖ (op a))).map
        ((Ideal.span {op b}).mkQ.restrictScalars k) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, Functor.mapLinearMap_apply,
      DistribSMul.toLinearMap_apply, smul_eq_mul, LinearMap.restrictScalars_apply,
      Submodule.mkQ_apply]
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [hev_apply]
      exact (stableModuleFunctor_map_cyclicModule_eq_zero_iff f).1 hf
    · rintro ⟨c, hc, rfl⟩
      have hm : Submodule.Quotient.mk c ∈
          LinearMap.ker (DistribSMul.toLinearMap k (Aᵐᵒᵖ ⧸ Ideal.span {op b}) (op a)) := by
        rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← Submodule.Quotient.mk_smul,
          smul_eq_mul, hc, Submodule.Quotient.mk_zero]
      refine ⟨e.symm ⟨_, hm⟩,
        (stableModuleFunctor_map_cyclicModule_eq_zero_iff _).2 ⟨c, hc, ?_⟩, ?_⟩
      · rw [← hev_apply]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨_, hm⟩).symm
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨_, hm⟩)
  -- The quotient functor is full, so rank-nullity for it gives the count.
  have : FiniteDimensional k (cyclicModule a ⟶ cyclicModule b) :=
    LinearEquiv.finiteDimensional e.symm
  have h := LinearMap.finrank_range_add_finrank_ker
    (F.mapLinearMap k (X := cyclicModule a) (Y := cyclicModule b))
  rw [LinearMap.range_eq_top.2 F.map_surjective, finrank_top, e.finrank_eq] at h
  rw [← h, ← hker, ← (Submodule.equivMapOfInjective ev hev _).finrank_eq]

end Stable

/-! ### The truncated polynomial algebra `K[X]/(X ^ n)` -/

section TruncatedPolynomial

open Polynomial

variable {K : Type u} [Field K] {n : ℕ}

/-- **Stable morphisms between the cyclic modules of `K[X]/(X ^ n)`.** With `x` the class of `X`
and `M_i = A ⧸ (x ^ i)`, the space of stable morphisms `M_i ⟶ M_j` has dimension
`min (min i j) (min (n - i) (n - j))` for `i, j ≤ n`, over any field `K`. -/
theorem finrank_stableModuleHom_cyclicModule_root_pow {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    finrank K ((stableModuleFunctor (AdjoinRoot (X ^ n : K[X]))).obj
        (cyclicModule (AdjoinRoot.root (X ^ n : K[X]) ^ i)) ⟶
      (stableModuleFunctor _).obj (cyclicModule (AdjoinRoot.root (X ^ n : K[X]) ^ j))) =
      min (min i j) (min (n - i) (n - j)) := by
  have := (monic_X_pow n).finite_adjoinRoot (R := K)
  have h := finrank_stableModuleHom_cyclicModule_add_finrank K
    (AdjoinRoot.root (X ^ n : K[X]) ^ i) (AdjoinRoot.root (X ^ n : K[X]) ^ j)
  rw [← (cyclicModuleHomEquiv K _).finrank_eq, finrank_cyclicModule_hom_root_pow hj,
    finrank_map_ker_smul_op_root_pow hi hj] at h
  omega

end TruncatedPolynomial

end FGModuleCat

end TauCeti
