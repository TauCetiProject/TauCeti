/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.RingTheory.Flat.ProjectiveDimension

/-!
# The projective dimension of a sequential colimit of modules

Let `F₀ → F₁ → F₂ → ⋯` be a sequence of `R`-modules, a functor `F : ℕ ⥤ ModuleCat R`, with
colimit `M`. Dimension shifting along the telescope short exact sequence
`0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → M → 0` (`ModuleCat.shortExact_telescopeShortComplex`) shows that if every
`Fₙ` has projective dimension at most `d`, then `M` has projective dimension at most `d + 1`: the
direct sum `⨁ₙ Fₙ` has projective dimension at most `d`, as coproducts of modules are exact.

The bound is sharp: `ℚ` is the colimit of `ℤ →2 ℤ →3 ℤ →4 ⋯` (multiplication by `n + 2` at the
`n`-th step) of free `ℤ`-modules but is not projective.

This is how a bound on the projective dimension of modules over the stages of a sequential
colimit of rings leads to a bound over the colimit. Let `R` be the union of an increasing
sequence of subrings `S₀ ⊆ S₁ ⊆ ⋯` and flat over each of them. Every `R`-module `M` is the colimit
of the base changes `R ⊗[Sₙ] M`, since each element of `R` already lies in some `Sₙ`, and flat
base change does not increase projective dimension. So if all modules over all `Sₙ` have
projective dimension at most `d`, then all `R`-modules have projective dimension at most `d + 1`.
The perfection of a regular ring of characteristic `p` is the main example.

## Main declarations

* `ModuleCat.hasProjectiveDimensionLT_succ_of_isColimit`: the colimit of a sequence of modules of
  projective dimension `< n` has projective dimension `< n + 1`.
* `ModuleCat.hasProjectiveDimensionLT_succ_of_iSup_eq_top`: if `R` is the union of an increasing
  sequence of subrings over each of which it is flat, and all modules over these subrings have
  projective dimension `< n`, then all `R`-modules have projective dimension `< n + 1`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), proof of Proposition 11.31.
-/

public section

open CategoryTheory Limits DirectSum TensorProduct

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (F : ℕ ⥤ ModuleCat.{v} R)

/-- The colimit of a sequence of modules of projective dimension `< n` has projective dimension
`< n + 1`. In terms of `HasProjectiveDimensionLE`, a sequential colimit of modules of projective
dimension at most `d` has projective dimension at most `d + 1`. -/
theorem hasProjectiveDimensionLT_succ_of_isColimit [Small.{v} R] {c : Cocone F} (hc : IsColimit c)
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (F.obj i) n) :
    HasProjectiveDimensionLT c.pt (n + 1) := by
  have : AB4OfSize.{0} (ModuleCat.{v} R) := AB4OfSize_shrink.{0, v} _
  have hsum (m : ℕ) (hm : n ≤ m) : HasProjectiveDimensionLT (of R (⨁ i, F.obj i)) m :=
    hasProjectiveDimensionLT_of_isColimit_cofan (coproductCoconeIsColimit fun i ↦ F.obj i) m
      fun i ↦ hasProjectiveDimensionLT_of_ge _ n m hm
  have hS := shortExact_telescopeShortComplex F hc
  rw [← telescopeShortComplex_X₃ F c]
  exact hS.hasProjectiveDimensionLT_X₃ n (telescopeShortComplex_X₁ F c ▸ hsum n le_rfl)
    (telescopeShortComplex_X₂ F c ▸ hsum (n + 1) n.le_succ)

end ModuleCat

namespace ModuleCat

section Subring

variable {R : Type u} [CommRing R]

section

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- In `R ⊗[B] M`, for a subring `B` of `R`, an element `r ∈ B` can be moved across the tensor
sign: `r ⊗ m = 1 ⊗ r • m`. -/
private theorem tmul_eq_one_tmul_smul {B : Subring R} {r : R} (hr : r ∈ B) (m : M) :
    r ⊗ₜ[B] m = (1 : R) ⊗ₜ (r • m) := by
  simpa [Subring.smul_def] using smul_tmul (⟨r, hr⟩ : B) (1 : R) m

/-- For subrings `A ≤ B` of `R`, the map `R ⊗[A] M → R ⊗[B] M`, `r ⊗ m ↦ r ⊗ m`. -/
private noncomputable def tensorSubringMap {A B : Subring R} (h : A ≤ B) :
    R ⊗[A] M →ₗ[R] R ⊗[B] M :=
  have : CompatibleSMul B A R M := ⟨fun a r m ↦ by
    simpa [Subring.smul_def] using smul_tmul (⟨a, h a.2⟩ : B) r m⟩
  mapOfCompatibleSMul B A R R M

@[simp]
private theorem tensorSubringMap_tmul {A B : Subring R} (h : A ≤ B) (r : R) (m : M) :
    tensorSubringMap M h (r ⊗ₜ m) = r ⊗ₜ m :=
  rfl

variable {S : ℕ → Subring R} (hS : Monotone S)

/-- The sequence `n ↦ R ⊗[S n] M` of base changes of `M` along an increasing sequence of
subrings. -/
private noncomputable abbrev tensorSubringFunctor : ℕ ⥤ ModuleCat.{u} R where
  obj n := of R (R ⊗[S n] M)
  map f := ofHom (tensorSubringMap M (hS f.le))
  map_id n := by
    ext : 1
    exact AlgebraTensorModule.ext fun r m ↦ by simp
  map_comp f g := by
    ext : 1
    exact AlgebraTensorModule.ext fun r m ↦ by simp

/-- The cocone over `tensorSubringFunctor M hS` with point `M` and legs `r ⊗ m ↦ r • m`. -/
private noncomputable abbrev tensorSubringCocone : Cocone (tensorSubringFunctor M hS) where
  pt := of R M
  ι :=
    { app n := ofHom (LinearMap.liftBaseChange R (LinearMap.id : M →ₗ[S n] M))
      naturality i j f := by
        ext : 1
        exact AlgebraTensorModule.ext fun r m ↦ by simp }

variable {M hS}

/-- The leg at stage `n` of a cocone over `tensorSubringFunctor M hS`, as an `R`-linear map out of
`R ⊗[S n] M`. -/
private noncomputable abbrev leg (s : Cocone (tensorSubringFunctor M hS)) (n : ℕ) :
    R ⊗[S n] M →ₗ[R] s.pt :=
  (s.ι.app n).hom

/-- The legs of a cocone over `tensorSubringFunctor M hS` agree on `1 ⊗ m` at every stage. -/
private theorem leg_one_tmul (s : Cocone (tensorSubringFunctor M hS)) (n : ℕ) (m : M) :
    leg s n ((1 : R) ⊗ₜ m) = leg s 0 ((1 : R) ⊗ₜ m) := by
  simp only [leg, ← s.w (homOfLE (Nat.zero_le n))]
  simp

/-- `m ↦ leg s 0 (1 ⊗ m)` is `R`-linear when the `S n` exhaust `R`: for `r ∈ S k`, the element
`1 ⊗ r • m` is `r • (1 ⊗ m)` at stage `k`. -/
private theorem leg_one_tmul_smul (htop : ∀ r, ∃ n, r ∈ S n)
    (s : Cocone (tensorSubringFunctor M hS)) (r : R) (m : M) :
    leg s 0 ((1 : R) ⊗ₜ (r • m)) = r • leg s 0 ((1 : R) ⊗ₜ m) := by
  obtain ⟨k, hk⟩ := htop r
  rw [← leg_one_tmul s k, ← leg_one_tmul s k, ← tmul_eq_one_tmul_smul M hk,
    tmul_eq_smul_one_tmul, map_smul]

/-- When the subrings `S n` exhaust `R`, the module `M` is the colimit of the base changes
`R ⊗[S n] M`. -/
private noncomputable def isColimitTensorSubringCocone (htop : ∀ r, ∃ n, r ∈ S n) :
    IsColimit (tensorSubringCocone M hS) where
  desc s := ofHom
    { toFun m := leg s 0 ((1 : R) ⊗ₜ m)
      map_add' m m' := by simp [tmul_add]
      map_smul' := leg_one_tmul_smul htop s }
  fac s n := by
    ext : 1
    refine AlgebraTensorModule.ext fun r m ↦ ?_
    have h : leg s n (r ⊗ₜ m) = r • leg s 0 ((1 : R) ⊗ₜ m) := by
      rw [← leg_one_tmul s n, tmul_eq_smul_one_tmul, map_smul]
    simpa [← leg_one_tmul_smul htop s r m] using h.symm
  uniq s g hg := by
    ext m
    simpa using congr($(hg 0).hom ((1 : R) ⊗ₜ m))

end

/-- If `R` is the union of an increasing sequence of subrings `S k` over each of which it is flat,
and every module over every `S k` has projective dimension `< n`, then every `R`-module has
projective dimension `< n + 1`. In terms of `HasProjectiveDimensionLE`, global dimension at most
`d` for all the `S k` gives global dimension at most `d + 1` for `R`. -/
theorem hasProjectiveDimensionLT_succ_of_iSup_eq_top {S : ℕ → Subring R} (hS : Monotone S)
    (htop : ⨆ k, S k = ⊤) [∀ k, Module.Flat (S k) R] {n : ℕ}
    (h : ∀ k (N : ModuleCat.{u} (S k)), HasProjectiveDimensionLT N n) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLT M (n + 1) := by
  have htop' (r : R) : ∃ k, r ∈ S k :=
    (Subring.mem_iSup_of_directed hS.directed_le).1 (htop ▸ Subring.mem_top r)
  exact hasProjectiveDimensionLT_succ_of_isColimit (tensorSubringFunctor M hS)
    (isColimitTensorSubringCocone htop') n fun k ↦
      hasProjectiveDimensionLT_tensorProduct R M (h k (of (S k) M))

end Subring

end ModuleCat
