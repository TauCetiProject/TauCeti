/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Lie.Abelian

/-!
# Homomorphisms from quotients by Lie ideals

Mathlib equips the quotient of a Lie algebra by a Lie ideal with its Lie algebra structure and
provides the quotient homomorphism `LieIdeal.mkQ`, its surjectivity, and its kernel. This file
gives its universal property: a homomorphism killing the ideal factors uniquely through the
quotient. A Lie subalgebra complementary to the ideal is isomorphic to the quotient. For a
surjective homomorphism, the induced map from the quotient by its kernel is an isomorphism, which
is the first isomorphism theorem.

These declarations live in the root `LieIdeal` and `LieHom` namespaces, extending Mathlib's API
and supporting receiver notation on the ideal and the homomorphism.

The functorial quotient-map and central-kernel API is adapted from
`Mei/Algebra/Lie/Quotient/Map.lean`, copyright (c) 2026 Mei contributors,
at commit `7f1e4c7714fb020473694755ad8748c8f15d0e7f`:
https://github.com/yuma-mizuno-lean/Mei/blob/7f1e4c7714fb020473694755ad8748c8f15d0e7f/Mei/Algebra/Lie/Quotient/Map.lean

## Main definitions

* `LieIdeal.quotEquivOfEq`: the Lie equivalence between quotients by equal ideals.
* `LieIdeal.liftQ`: the homomorphism `L ⧸ I →ₗ⁅R⁆ L'` induced by a homomorphism
  `L →ₗ⁅R⁆ L'` whose kernel contains `I`.
* `LieIdeal.factor`: the transition `L ⧸ I →ₗ⁅R⁆ L ⧸ J` between the quotients by nested ideals
  `I ≤ J`.
* `LieIdeal.quotientEquivOfIsCompl`: the isomorphism `L ⧸ I ≃ₗ⁅R⁆ S` for a Lie subalgebra `S`
  complementary to `I`.
* `LieHom.quotKerEquivOfSurjective`: the first isomorphism theorem, identifying the quotient of
  `L` by the kernel of a surjective homomorphism with its target.

## Main results

* `LieIdeal.liftQ_mkQ`: the lifted homomorphism restricts to the original one along the quotient
  map.
* `LieIdeal.coe_liftQ`: the lifted homomorphism is `Submodule.liftQ` of the underlying linear map.
* `LieIdeal.liftQ_injective_iff` and `LieIdeal.liftQ_surjective`: the lifted homomorphism is
  injective exactly when the ideal exhausts the kernel, and surjective when the original
  homomorphism is.
* `LieIdeal.lieHom_qext`: two homomorphisms from the quotient are equal when they agree after the
  quotient map.
* `LieIdeal.eq_liftQ`: the lifted homomorphism is the unique such factorization.
* `LieIdeal.ker_liftQ_mkQ`: for ideals `J ≤ I`, the kernel of `L ⧸ J → L ⧸ I` is the image of `I`.
* `LieIdeal.factor_refl`, `LieIdeal.factor_comp` and `LieIdeal.factor_surjective`: the transitions
  between nested quotients are the identity at equal ideals, compose, and are surjective.
* `LieIdeal.coe_mkQ`: the linear map underlying `LieIdeal.mkQ` is the quotient map of submodules.
* `LieIdeal.mkQ_comp_incl_surjective`: a Lie subalgebra `P` with `I + P = L` maps onto `L ⧸ I`.
* `LieIdeal.ker_mkQ_comp_incl`: the kernel of `P → L ⧸ I` is the ideal `I ∩ P` of `P`.
* `LieIdeal.isCompl_map_incl`: a complement of `I ∩ P` inside a supplement `P` of `I` is a
  complement of `I` in `L`.

The transitions `LieIdeal.factor` and their lemmas are adapted from
`Mei/Algebra/Lie/Quotient/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace LieIdeal

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (I : LieIdeal R L)

/-- Quotienting by equal Lie ideals gives equivalent Lie algebras, refining
`Submodule.quotEquivOfEq` by retaining the Lie bracket. -/
def quotEquivOfEq (J : LieIdeal R L) (h : I = J) : (L ⧸ I) ≃ₗ⁅R⁆ L ⧸ J where
  __ := Submodule.quotEquivOfEq I.toSubmodule J.toSubmodule (congrArg LieSubmodule.toSubmodule h)
  map_lie' {x y} := by
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    -- The underlying quotient equivalence preserves representatives definitionally.
    rfl

/-- The equivalence between quotients by equal ideals preserves representatives. -/
@[simp]
theorem quotEquivOfEq_mk (J : LieIdeal R L) (h : I = J) (x : L) :
    I.quotEquivOfEq J h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x :=
  Submodule.quotEquivOfEq_mk _ _ (congrArg LieSubmodule.toSubmodule h) x

/-- The inverse equivalence between quotients by equal ideals preserves representatives. -/
@[simp]
theorem quotEquivOfEq_symm_mk (J : LieIdeal R L) (h : I = J) (x : L) :
    (I.quotEquivOfEq J h).symm (LieSubmodule.Quotient.mk x) =
      LieSubmodule.Quotient.mk x := by
  apply (I.quotEquivOfEq J h).injective
  simp

/-- The homomorphism `L ⧸ I →ₗ⁅R⁆ L'` induced by a homomorphism `f : L →ₗ⁅R⁆ L'` whose kernel
contains the ideal `I`. -/
def liftQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) : L ⧸ I →ₗ⁅R⁆ L' where
  __ := LieSubmodule.toSubmodule I |>.liftQ (f : L →ₗ[R] L') h
  map_lie' {x y} := by
    induction x using Quotient.inductionOn' with | _ x
    induction y using Quotient.inductionOn' with | _ y
    exact f.map_lie x y

/-- The induced homomorphism on the quotient sends the class of `x` to `f x`. -/
@[simp]
theorem liftQ_apply (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) (x : L) :
    I.liftQ f h (LieSubmodule.Quotient.mk x) = f x := (rfl)

/-- The linear map underlying the induced homomorphism on the quotient is `Submodule.liftQ` of
the linear map underlying `f`. -/
theorem coe_liftQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) :
    ((I.liftQ f h : L ⧸ I →ₗ⁅R⁆ L') : L ⧸ I →ₗ[R] L') =
      (LieSubmodule.toSubmodule I).liftQ (f : L →ₗ[R] L')
        (((LieSubmodule.toSubmodule_le_toSubmodule I f.ker).mpr h).trans
          (LieHom.ker_toSubmodule f).le) :=
  (rfl)

/-- The homomorphism induced on the quotient is injective exactly when the ideal quotiented by
exhausts the kernel. -/
theorem liftQ_injective_iff (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) :
    Function.Injective (I.liftQ f h) ↔ f.ker ≤ I := by
  refine ⟨fun hf x hx => I.mkQ_eq_zero.1 (hf (by simpa using hx)), fun h' => ?_⟩
  rw [← LieHom.coe_toLinearMap, ← LinearMap.ker_eq_bot, coe_liftQ]
  exact Submodule.ker_liftQ_eq_bot _ (f : L →ₗ[R] L') _ <| by
    rw [← LieHom.ker_toSubmodule, LieSubmodule.toSubmodule_le_toSubmodule]; exact h'

/-- The homomorphism induced on the quotient by a surjective homomorphism is surjective. -/
theorem liftQ_surjective (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) (h' : Function.Surjective f) :
    Function.Surjective (I.liftQ f h) := by
  rw [← LieHom.coe_toLinearMap, ← LinearMap.range_eq_top, coe_liftQ, Submodule.range_liftQ,
    LinearMap.range_eq_top, LieHom.coe_toLinearMap]
  exact h'

/-- The induced homomorphism on the quotient composed with the quotient map is the original
homomorphism. -/
@[simp]
theorem liftQ_mkQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) : (I.liftQ f h).comp I.mkQ = f := by
  ext x
  simp

/-- Two homomorphisms out of `L ⧸ I` that agree after composition with the quotient map are
equal. -/
@[ext high]
theorem lieHom_qext {g₁ g₂ : L ⧸ I →ₗ⁅R⁆ L'} (h : ∀ x : L, g₁ (I.mkQ x) = g₂ (I.mkQ x)) :
    g₁ = g₂ := by
  apply LieHom.ext
  exact LinearMap.congr_fun <|
    Submodule.quot_hom_ext I.toSubmodule g₁.toLinearMap g₂.toLinearMap fun x => h x

/-- The factorization of `LieIdeal.liftQ` is the only one: a homomorphism out of `L ⧸ I`
restricting to `f` along the quotient map is `I.liftQ f h`. -/
theorem eq_liftQ {f : L →ₗ⁅R⁆ L'} {h : I ≤ f.ker} {g : L ⧸ I →ₗ⁅R⁆ L'}
    (hg : ∀ x : L, g (I.mkQ x) = f x) : g = I.liftQ f h :=
  I.lieHom_qext fun x => by rw [hg]; simp

/-- For ideals `J ≤ I`, the kernel of the induced map `L ⧸ J → L ⧸ I` is the image of `I` in
`L ⧸ J`. -/
theorem ker_liftQ_mkQ {J : LieIdeal R L} (h : J ≤ I.mkQ.ker) :
    (J.liftQ I.mkQ h).ker = I.map J.mkQ := by
  rw [← LieSubmodule.toSubmodule_inj, LieHom.ker_toSubmodule, coe_liftQ, Submodule.ker_liftQ,
    ← LieHom.ker_toSubmodule, mkQ_ker, coe_map_of_surjective J.surjective_mkQ]
  rfl

/-- The linear map underlying the quotient homomorphism is the quotient map of submodules. -/
theorem coe_mkQ : (I.mkQ : L →ₗ[R] L ⧸ I) = I.toSubmodule.mkQ := (rfl)

/-- The transition from the quotient by a smaller ideal to the quotient by a larger ideal. This is
the Lie algebra analogue of `Submodule.factor`. -/
def factor {I J : LieIdeal R L} (h : I ≤ J) : L ⧸ I →ₗ⁅R⁆ L ⧸ J :=
  I.liftQ J.mkQ (by rwa [mkQ_ker])

/-- A quotient transition sends each class to the class of the same representative. -/
@[simp]
theorem factor_apply {I J : LieIdeal R L} (h : I ≤ J) (x : L) :
    factor h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk x := by
  simp [factor]

/-- A quotient transition commutes with the quotient projections. -/
@[simp]
theorem factor_mkQ {I J : LieIdeal R L} (h : I ≤ J) : (factor h).comp I.mkQ = J.mkQ :=
  I.liftQ_mkQ J.mkQ _

/-- A quotient transition at the same ideal is the identity. -/
@[simp]
theorem factor_refl : factor (le_refl I) = LieHom.id := by
  ext x
  simp [mkQ_apply]

/-- Successive quotient transitions compose to the direct transition. -/
@[simp]
theorem factor_comp {I J K : LieIdeal R L} (hIJ : I ≤ J) (hJK : J ≤ K) :
    (factor hJK).comp (factor hIJ) = factor (hIJ.trans hJK) := by
  ext x
  simp [mkQ_apply]

/-- Quotient transitions are surjective. -/
theorem factor_surjective {I J : LieIdeal R L} (h : I ≤ J) : Function.Surjective (factor h) :=
  liftQ_surjective _ _ _ J.surjective_mkQ

section Supplement

variable {P : LieSubalgebra R L}

/-- A Lie subalgebra `P` supplementing an ideal `I`, in the sense that `I + P = L`, maps onto the
quotient `L ⧸ I`. -/
theorem mkQ_comp_incl_surjective (hIP : Codisjoint I.toSubmodule P.toSubmodule) :
    Function.Surjective (I.mkQ.comp P.incl) := by
  intro y
  obtain ⟨x, rfl⟩ := I.surjective_mkQ y
  obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.1 (hIP.eq_top ▸ Submodule.mem_top (x := x))
  refine ⟨⟨s, hs⟩, ?_⟩
  rw [LieHom.comp_apply, LieSubalgebra.coe_incl, ← sub_eq_zero, ← map_sub, ← LieHom.mem_ker,
    mkQ_ker, Subtype.coe_mk, sub_add_cancel_right]
  exact I.neg_mem hi

/-- The kernel of the map `P → L ⧸ I` induced by a Lie subalgebra `P` is the ideal `I ∩ P` of
`P`. -/
@[simp]
theorem ker_mkQ_comp_incl : (I.mkQ.comp P.incl).ker = I.comap P.incl := by
  ext x
  rw [LieHom.mem_ker, mem_comap, LieHom.comp_apply, mkQ_apply, LieSubmodule.Quotient.mk_eq_zero']

end Supplement

section IsCompl

variable (S : LieSubalgebra R L) (h : IsCompl I.toSubmodule S.toSubmodule)

/-- A Lie subalgebra `S` complementary to a Lie ideal `I` is isomorphic to the quotient `L ⧸ I`,
the class of `x : S` corresponding to `x`. This is the Lie algebra version of
`Submodule.quotientEquivOfIsCompl`, which is its underlying linear equivalence
(`LieIdeal.toLinearEquiv_quotientEquivOfIsCompl`). -/
noncomputable def quotientEquivOfIsCompl : (L ⧸ I) ≃ₗ⁅R⁆ S :=
  (LieEquiv.ofBijective (I.mkQ.comp S.incl) <| by
    convert (Submodule.quotientEquivOfIsCompl I.toSubmodule S.toSubmodule h).symm.bijective
    ext x
    simp [mkQ_apply]).symm

/-- The inverse of `LieIdeal.quotientEquivOfIsCompl` sends `x : S` to its class. -/
@[simp]
theorem quotientEquivOfIsCompl_symm_apply (x : S) :
    (I.quotientEquivOfIsCompl S h).symm x = LieSubmodule.Quotient.mk (x : L) := by
  simp [quotientEquivOfIsCompl]

/-- `LieIdeal.quotientEquivOfIsCompl` sends the class of `x : S` to `x`. -/
@[simp]
theorem quotientEquivOfIsCompl_apply_mk_coe (x : S) :
    I.quotientEquivOfIsCompl S h (LieSubmodule.Quotient.mk (x : L)) = x := by
  rw [← quotientEquivOfIsCompl_symm_apply I S h, LieEquiv.apply_symm_apply]

/-- The linear equivalence underlying `LieIdeal.quotientEquivOfIsCompl` is
`Submodule.quotientEquivOfIsCompl`. -/
theorem toLinearEquiv_quotientEquivOfIsCompl :
    (I.quotientEquivOfIsCompl S h).toLinearEquiv =
      Submodule.quotientEquivOfIsCompl I.toSubmodule S.toSubmodule h :=
  LinearEquiv.ext fun z => by
    obtain ⟨x, rfl⟩ :=
      (Submodule.quotientEquivOfIsCompl I.toSubmodule S.toSubmodule h).symm.surjective z
    simp only [LinearEquiv.apply_symm_apply, LieEquiv.coe_toLinearEquiv]
    -- `Submodule.quotientEquivOfIsCompl` inverts to `Submodule.Quotient.mk`, of which
    -- `LieSubmodule.Quotient.mk` is an abbreviation
    exact I.quotientEquivOfIsCompl_apply_mk_coe S h x

end IsCompl

end LieIdeal

namespace LieHom

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- **The first isomorphism theorem** for a surjective homomorphism of Lie algebras: the quotient
by its kernel is isomorphic to the target. -/
noncomputable def quotKerEquivOfSurjective (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) :
    (L ⧸ f.ker) ≃ₗ⁅R⁆ L' :=
  LieEquiv.ofBijective (f.ker.liftQ f le_rfl)
    ⟨(f.ker.liftQ_injective_iff f le_rfl).2 le_rfl, f.ker.liftQ_surjective f le_rfl hf⟩

/-- The first isomorphism theorem sends the class of `x` to `f x`. -/
@[simp]
theorem quotKerEquivOfSurjective_apply_mk (f : L →ₗ⁅R⁆ L') (hf : Function.Surjective f) (x : L) :
    f.quotKerEquivOfSurjective hf (LieSubmodule.Quotient.mk x) = f x := (rfl)

end LieHom

namespace TauCeti

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- The inverse of the first isomorphism theorem sends `f x` to the class of `x`. -/
@[simp]
theorem _root_.LieHom.quotKerEquivOfSurjective_symm_apply (f : L →ₗ⁅R⁆ L')
    (hf : Function.Surjective f) (x : L) :
    (f.quotKerEquivOfSurjective hf).symm (f x) = LieSubmodule.Quotient.mk x := by
  simpa only [LieHom.quotKerEquivOfSurjective_apply_mk] using
    (f.quotKerEquivOfSurjective hf).symm_apply_apply (LieSubmodule.Quotient.mk x)

variable (I : LieIdeal R L) {P : LieSubalgebra R L}

/-- **A complement inside a supplement.** If a Lie subalgebra `P` supplements an ideal `I`, then a
complement in `P` of the ideal `I ∩ P` of `P` is a complement of `I` in `L`. -/
theorem _root_.LieIdeal.isCompl_map_incl (hIP : Codisjoint I.toSubmodule P.toSubmodule)
    {J : LieSubalgebra R P} (hJ : IsCompl (I.comap P.incl).toSubmodule J.toSubmodule) :
    IsCompl I.toSubmodule (J.map P.incl).toSubmodule := by
  refine ⟨Submodule.disjoint_def.2 fun x hxI hxJ ↦ ?_,
    codisjoint_iff.2 (Submodule.eq_top_iff'.2 fun x ↦ ?_)⟩
  · obtain ⟨j, hj, rfl⟩ := (LieSubalgebra.mem_map ..).1 hxJ
    rw [Submodule.disjoint_def.1 hJ.disjoint j (LieIdeal.mem_comap.2 hxI) hj, map_zero]
  · obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.1 (hIP.eq_top ▸ Submodule.mem_top (x := x))
    obtain ⟨k, hk, j, hj, hkj⟩ := Submodule.mem_sup.1
      (hJ.codisjoint.eq_top ▸ Submodule.mem_top (x := (⟨s, hs⟩ : P)))
    refine Submodule.mem_sup.2 ⟨i + P.incl k, I.add_mem hi (LieIdeal.mem_comap.1 hk), P.incl j,
      (LieSubalgebra.mem_map ..).2 ⟨j, hj, rfl⟩, ?_⟩
    rw [add_assoc, ← map_add, hkj, LieSubalgebra.coe_incl]

end TauCeti

/-! ## Maps between quotients and central kernels -/

namespace LieIdeal

variable {R L L' L'' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']

variable (I : LieIdeal R L) (J : LieIdeal R L')

/-- The Lie homomorphism induced on quotients by a map carrying `I` into `J`. -/
def mapQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) : L ⧸ I →ₗ⁅R⁆ L' ⧸ J :=
  I.liftQ (J.mkQ.comp f) (by
    intro x hx
    rw [LieHom.mem_ker, LieHom.comp_apply, mkQ_apply,
      LieSubmodule.Quotient.mk_eq_zero']
    exact h hx)

/-- The underlying linear map is Mathlib's map between module quotients. -/
theorem toLinearMap_mapQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    (I.mapQ J f h).toLinearMap =
      I.toSubmodule.mapQ J.toSubmodule f.toLinearMap (by intro x hx; exact h hx) := by
  rw [mapQ, coe_liftQ]
  rfl

/-- The induced map sends the class of `x` to the class of `f x`. -/
@[simp]
theorem mapQ_apply (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) (x : L) :
    I.mapQ J f h (LieSubmodule.Quotient.mk x) = LieSubmodule.Quotient.mk (f x) := by
  simp [mapQ, LieHom.comp_apply]

/-- The square formed by the two quotient projections commutes. -/
@[simp]
theorem mapQ_mkQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    (I.mapQ J f h).comp I.mkQ = J.mkQ.comp f :=
  I.liftQ_mkQ (J.mkQ.comp f) _

/-- The identity induces the identity on a Lie quotient. -/
@[simp]
theorem mapQ_id (h : I ≤ I.comap (LieHom.id : L →ₗ⁅R⁆ L) := le_rfl) :
    I.mapQ I LieHom.id h = LieHom.id := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

/-- Passing to quotients respects composition of Lie homomorphisms. -/
theorem mapQ_comp (K : LieIdeal R L'') (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'')
    (hf : I ≤ J.comap f) (hg : J ≤ K.comap g)
    (hgf : I ≤ K.comap (g.comp f) := fun _ hx => hg (hf hx)) :
    I.mapQ K (g.comp f) hgf = (J.mapQ K g hg).comp (I.mapQ J f hf) := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

/-- A map between quotients making the quotient square commute exists exactly
when the original map carries the source ideal into the target ideal. -/
theorem exists_mapQ_iff (f : L →ₗ⁅R⁆ L') :
    (∃ g : L ⧸ I →ₗ⁅R⁆ L' ⧸ J, g.comp I.mkQ = J.mkQ.comp f) ↔
      I ≤ J.comap f := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    have hzero : I.mkQ x = 0 := by
      simpa only [mkQ_apply, LieSubmodule.Quotient.mk_eq_zero'] using hx
    have heq : (J.mkQ.comp f) x = 0 := by
      rw [← hg, LieHom.comp_apply, hzero, map_zero]
    rw [LieHom.comp_apply, mkQ_apply, LieSubmodule.Quotient.mk_eq_zero'] at heq
    exact mem_comap.mpr heq
  · intro h
    exact ⟨I.mapQ J f h, I.mapQ_mkQ J f h⟩

/-- The kernel on quotients is the image of the inverse image of the target ideal. -/
theorem ker_mapQ (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    (I.mapQ J f h).ker = (J.comap f).map I.mkQ := by
  rw [← LieSubmodule.toSubmodule_inj, LieHom.ker_toSubmodule,
    toLinearMap_mapQ, Submodule.ker_mapQ,
    coe_map_of_surjective I.surjective_mkQ]
  rfl

/-- The induced quotient map is injective exactly when the inverse image of the
target ideal contains no additional elements. -/
theorem mapQ_injective_iff (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f) :
    Function.Injective (I.mapQ J f h) ↔ J.comap f ≤ I := by
  rw [← LieHom.ker_eq_bot, ker_mapQ, LieIdeal.map_eq_bot_iff, mkQ_ker]

/-- Surjectivity of the original map implies surjectivity on quotients. -/
theorem mapQ_surjective (f : L →ₗ⁅R⁆ L') (h : I ≤ J.comap f)
    (hf : Function.Surjective f) : Function.Surjective (I.mapQ J f h) :=
  I.liftQ_surjective _ _ (J.surjective_mkQ.comp hf)

section Nested

variable (I J : LieIdeal R L)

/-- The identity induces the transition between nested quotient ideals. -/
theorem mapQ_id_eq_factor (h : I ≤ J) :
    I.mapQ J LieHom.id (fun _ hx => h hx) = factor h := by
  apply I.lieHom_qext
  intro x
  exact (I.mapQ_apply J LieHom.id h x).trans (factor_apply h x).symm

/-- An ideal has central image in the quotient by `I` exactly when all its
brackets with the ambient algebra belong to `I`. -/
theorem map_mkQ_le_center_iff :
    J.map I.mkQ ≤ LieAlgebra.center R (L ⧸ I) ↔ ⁅(⊤ : LieIdeal R L), J⁆ ≤ I := by
  rw [LieModule.le_max_triv_iff_bracket_eq_bot]
  have htop : (⊤ : LieIdeal R L).map I.mkQ = ⊤ := by
    rw [← LieHom.idealRange_eq_map,
      I.mkQ.idealRange_eq_top_of_surjective I.surjective_mkQ]
  rw [← htop, ← LieIdeal.map_bracket_eq _ I.surjective_mkQ,
    LieIdeal.map_eq_bot_iff, mkQ_ker]

/-- A quotient transition is a central extension exactly when bracketing with
the larger ideal lands in the smaller ideal. -/
theorem ker_factor_le_center_iff (h : I ≤ J) :
    (factor h).ker ≤ LieAlgebra.center R (L ⧸ I) ↔
      ⁅(⊤ : LieIdeal R L), J⁆ ≤ I := by
  rw [factor, J.ker_liftQ_mkQ]
  exact I.map_mkQ_le_center_iff J

end Nested

/-- Induced maps commute with the transitions obtained by enlarging the source
and target ideals. -/
theorem factor_comp_mapQ (I' : LieIdeal R L) (J' : LieIdeal R L')
    (hI : I ≤ I') (hJ : J ≤ J') (f : L →ₗ⁅R⁆ L')
    (hf : I ≤ J.comap f) (hf' : I' ≤ J'.comap f) :
    (factor hJ).comp (I.mapQ J f hf) =
      (I'.mapQ J' f hf').comp (factor hI) := by
  apply I.lieHom_qext
  intro x
  simp [mkQ_apply]

end LieIdeal
