/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.RingTheory.GlobalDimension
public import TauCeti.RingTheory.Jacobson.Semiprimary

/-!
# The global dimension of a semiprimary ring

A ring `A` is semiprimary when its Jacobson radical `J` is nilpotent and `A ⧸ J` is a semisimple
ring; Artinian rings, and in particular Artin algebras, are semiprimary. Auslander's theorem says
that the global dimension of such a ring is the projective dimension of the single module `A ⧸ J`.
The ring need not be Noetherian, and no finiteness is asked of the modules.

There are two steps. A module annihilated by a two-sided ideal `I` with `A ⧸ I` semisimple is a
quotient of a direct sum of copies of the semisimple module `A ⧸ I`, hence a direct summand of it,
so its projective dimension is at most that of `A ⧸ I`. Every module `M` over a semiprimary ring
has the finite filtration `M ⊇ J • M ⊇ J² • M ⊇ ⋯ ⊇ 0` whose layers are annihilated by `J`
(`IsSemiprimaryRing.induction`), and projective dimension bounds pass through extensions.

The quotient `A ⧸ J` lives in the universe of `A`; for modules in another universe `v` it is
replaced by `Shrink.{v} (A ⧸ J)`, as in `TauCeti.globalDimension_le_tfae`.

## Main results

* `LinearMap.hasProjectiveDimensionLT_of_surjective`: a quotient of a direct sum of copies of a
  semisimple module `X` has projective dimension at most that of `X`.
* `Module.IsTorsionBySet.hasProjectiveDimensionLT`: if `A ⧸ I` is a semisimple ring, a module
  annihilated by `I` has projective dimension at most that of `A ⧸ I`.
* `ModuleCat.hasProjectiveDimensionLT_of_isSemiprimaryRing`: over a semiprimary ring, every module
  has projective dimension at most that of `A ⧸ J`.
* `TauCeti.globalDimension_eq_projectiveDimension_quotient_jacobson`: **Auslander's theorem**, the
  global dimension of a semiprimary ring is the projective dimension of `A ⧸ J`.

## References

* M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math.
  J. 9 (1955), 67–77, Corollary 9 and Corollary 11 (b), p. 73.
-/

public section

universe v u

open CategoryTheory Limits DirectSum

variable {A : Type u} [Ring A] [Small.{v} A]

/-- A quotient of a direct sum of copies of a semisimple module `X` has projective dimension at
most that of `X`: the quotient map splits, so the quotient is a direct summand of the direct sum,
and a direct sum of modules of projective dimension `< n` has projective dimension `< n`. -/
theorem LinearMap.hasProjectiveDimensionLT_of_surjective {X M : ModuleCat.{v} A}
    [IsSemisimpleModule A X] {ι : Type v} (f : (ι →₀ X) →ₗ[A] M) (hf : Function.Surjective f)
    (n : ℕ) [HasProjectiveDimensionLT X n] : HasProjectiveDimensionLT M n := by
  classical
  let e := finsuppLEquivDirectSum A X ι
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property f hf LinearMap.id
  have : HasProjectiveDimensionLT (ModuleCat.of A (⨁ _ : ι, X)) n :=
    hasProjectiveDimensionLT_of_isColimit_cofan
      (ModuleCat.coproductCoconeIsColimit.{u, v, 0} fun _ : ι ↦ X) n fun _ ↦ inferInstance
  exact (Retract.mk (X := M) (Y := ModuleCat.of A (⨁ _ : ι, X))
    (ModuleCat.ofHom (e.toLinearMap ∘ₗ s)) (ModuleCat.ofHom (f ∘ₗ e.symm.toLinearMap))
    (by ext x; simpa using LinearMap.congr_fun hs x)).hasProjectiveDimensionLT n

/-- **Modules annihilated by an ideal with semisimple quotient.** If `I` is a two-sided ideal with
`A ⧸ I` a semisimple ring, then every module annihilated by `I` has projective dimension `< n` as
soon as `A ⧸ I` does: it is a quotient, hence a direct summand, of a direct sum of copies of the
semisimple module `A ⧸ I`. -/
theorem Module.IsTorsionBySet.hasProjectiveDimensionLT {I : Ideal A} [I.IsTwoSided]
    [IsSemisimpleRing (A ⧸ I)] {M : ModuleCat.{v} A} (hM : Module.IsTorsionBySet A M I) (n : ℕ)
    [HasProjectiveDimensionLT (ModuleCat.of A (Shrink.{v} (A ⧸ I))) n] :
    HasProjectiveDimensionLT M n := by
  have : IsSemisimpleModule A (A ⧸ I) := by
    have := TauCeti.isSemisimpleModule_quotient_smul_top A I A
    rwa [smul_eq_mul, Ideal.mul_top] at this
  have : IsSemisimpleModule A (Shrink.{v} (A ⧸ I)) := .congr (Shrink.linearEquiv A (A ⧸ I))
  -- The map `A ⧸ I → M` sending `1` to `m`, which exists because `I` annihilates `M`.
  let φ (m : M) : Shrink.{v} (A ⧸ I) →ₗ[A] M :=
    I.liftQ (LinearMap.toSpanSingleton A M m)
        (fun a ha ↦ LinearMap.mem_ker.mpr (hM (a := ⟨a, ha⟩))) ∘ₗ
      (Shrink.linearEquiv A (A ⧸ I)).toLinearMap
  refine LinearMap.hasProjectiveDimensionLT_of_surjective
    (X := ModuleCat.of A (Shrink.{v} (A ⧸ I))) (Finsupp.lsum ℕ φ) (fun m ↦
      ⟨Finsupp.single m ((Shrink.linearEquiv A (A ⧸ I)).symm (Submodule.Quotient.mk 1)), ?_⟩) n
  simp only [Finsupp.lsum_single, φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

/-- Over a semiprimary ring `A`, with Jacobson radical `J`, every module has projective dimension
`< n` as soon as `A ⧸ J` does. The layers of the filtration `M ⊇ J • M ⊇ J² • M ⊇ ⋯ ⊇ 0` are
annihilated by `J`, and projective dimension bounds pass through extensions. -/
theorem ModuleCat.hasProjectiveDimensionLT_of_isSemiprimaryRing [IsSemiprimaryRing A]
    (M : ModuleCat.{v} A) (n : ℕ)
    [HasProjectiveDimensionLT (ModuleCat.of A (Shrink.{v} (A ⧸ Ring.jacobson A))) n] :
    HasProjectiveDimensionLT M n := by
  refine IsSemiprimaryRing.induction ℤ A M
    (P := fun N _ _ _ ↦ HasProjectiveDimensionLT (ModuleCat.of A N) n)
    (fun N _ _ _ _ _ hJ ↦ hJ.hasProjectiveDimensionLT (M := ModuleCat.of A N) n)
    (fun N _ _ _ _ hK hQ ↦ ?_)
  -- Extend along the short exact sequence `0 → J • N → N → N ⧸ J • N → 0`.
  let K : Submodule A N := Ring.jacobson A • ⊤
  have hS := ModuleCat.shortComplex_shortExact
    (ModuleCat.shortComplexOfCompEqZero K.subtype K.mkQ
      (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero)
    (LinearMap.exact_subtype_mkQ K) K.injective_subtype K.mkQ_surjective
  exact hS.hasProjectiveDimensionLT_X₂ n hK hQ

namespace TauCeti

/-- **Auslander's theorem.** The global dimension of a semiprimary ring `A`, for instance an
Artinian ring, is the projective dimension of `A ⧸ J`, where `J` is the Jacobson radical. Both
sides are `⊥` for the zero ring. Auslander, *On the dimension of modules and algebras III*,
Corollary 11 (b). -/
theorem globalDimension_eq_projectiveDimension_quotient_jacobson [IsSemiprimaryRing A] :
    globalDimension.{v} A =
      projectiveDimension (ModuleCat.of A (Shrink.{v} (A ⧸ Ring.jacobson A))) :=
  le_antisymm ((globalDimension_le_iff A _).mpr fun M ↦
      projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
        M.hasProjectiveDimensionLT_of_isSemiprimaryRing n)
    (ModuleCat.projectiveDimension_le_globalDimension _)

end TauCeti
