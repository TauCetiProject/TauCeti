/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Dynamics.PeriodicPts.Finite
public import TauCeti.LinearAlgebra.End.RangePow

/-!
# Hida's ordinary projector on a finite module

Let `M` be a module whose underlying type is finite and let `U` be an endomorphism of `M`. The
**ordinary projector** of `U` is `e_U = U ^ (Nat.card M)!`
(`Module.End.ordinaryProjection`). It is the limit of the factorial powers of `U` in the discrete
topology: `e_U = U ^ n !` for every `n ≥ Nat.card M`
(`Module.End.ordinaryProjection_eq_pow_factorial`). Its range, the *ordinary part* of `M`, is the
set of `U`-periodic vectors, and its kernel, the *non-ordinary part*, consists of the vectors
killed by `U ^ Nat.card M`.

The main results are:

* `Module.End.isIdempotentElem_ordinaryProjection`, `Module.End.commute_ordinaryProjection`:
  `e_U` is an idempotent commuting with `U`;
* `Module.End.range_ordinaryProjection_eq_iInf`, `Module.End.ker_ordinaryProjection_eq_iSup`,
  `Module.End.ordinaryProjection_eq_projection`: `e_U` is the projection of Mathlib's Fitting
  decomposition `M = (⨅ n, range (U ^ n)) ⊕ (⨆ n, ker (U ^ n))`;
* `Module.End.range_ordinaryProjection_mem_invtSubmodule`,
  `Module.End.ker_ordinaryProjection_mem_invtSubmodule`: both parts are `U`-stable;
* `Module.End.ordinaryEquiv`, `Module.End.bijOn_range_ordinaryProjection`,
  `Module.End.invOn_range_ordinaryProjection`: `U` restricts to a linear automorphism of the
  ordinary part, with inverse `U ^ ((Nat.card M)! - 1)`;
* `Module.End.range_ordinaryProjection_eq_of_isCompl`,
  `Module.End.ker_ordinaryProjection_eq_of_isCompl`: uniqueness of the decomposition into a
  summand on which `U` is surjective and a summand on which `U` is locally nilpotent;
* `Module.End.ordinaryProjection_comp_eq_comp_ordinaryProjection`,
  `Module.End.ordinaryProjection_apply_comm`: naturality for equivariant maps between finite
  modules;
* `Module.End.map_range_ordinaryProjection_of_exact`,
  `Module.End.map_range_ordinaryProjection_of_surjective` and their kernel versions: taking
  ordinary and non-ordinary parts is exact on equivariant exact sequences of finite modules; in
  particular the ordinary part of a quotient by a `U`-stable submodule is the image of the
  ordinary part (`Module.End.range_ordinaryProjection_mapQ`).

These are the finite-level statements behind Hida's ordinary projector `e = lim U^{n!}` on
profinite and adically complete modules, where `e` is obtained from its reductions to finite
quotients.

## References

* H. Hida, *Iwasawa modules attached to congruences of cusp forms*, Ann. Sci. École Norm. Sup.
  (4) 19 (1986), §1.
* C. Khare, J. Thorne, *Potential automorphy and the Leopoldt conjecture*, Amer. J. Math. 139
  (2017), §2.4, Lemmas 2.10 and 2.11.
-/

public section

open Function LinearMap Nat

namespace Module.End

variable {R M N P : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- Hida's ordinary projector `U ^ (Nat.card M)!` of an endomorphism `U` of a finite module `M`.
It is an idempotent commuting with `U`, and equals `U ^ n !` for every `n ≥ Nat.card M`. If `M`
is infinite then `Nat.card M = 0` and this is the junk value `U`. -/
noncomputable def ordinaryProjection (U : Module.End R M) : Module.End R M :=
  U ^ (Nat.card M)!

theorem ordinaryProjection_def (U : Module.End R M) :
    U.ordinaryProjection = U ^ (Nat.card M)! := by
  rw [ordinaryProjection]

/-- An endomorphism commutes with its ordinary projector. -/
theorem commute_ordinaryProjection (U : Module.End R M) : Commute U U.ordinaryProjection :=
  (Commute.refl U).pow_right _

/-- The ordinary projector commutes with every power of `U`, applied form:
`e_U ((U ^ k) x) = (U ^ k) (e_U x)`. -/
theorem ordinaryProjection_pow_apply_comm (U : Module.End R M) (k : ℕ) (x : M) :
    U.ordinaryProjection ((U ^ k) x) = (U ^ k) (U.ordinaryProjection x) :=
  LinearMap.congr_fun ((commute_ordinaryProjection U).pow_left k).eq.symm x

/-- The ordinary part is `U`-stable. -/
theorem range_ordinaryProjection_mem_invtSubmodule (U : Module.End R M) :
    range U.ordinaryProjection ∈ U.invtSubmodule := by
  rw [ordinaryProjection_def]
  exact (mem_invtSubmodule_iff_mapsTo _).mpr (LinearMap.mapsTo_range_pow U _)

/-- The non-ordinary part is `U`-stable. -/
theorem ker_ordinaryProjection_mem_invtSubmodule (U : Module.End R M) :
    ker U.ordinaryProjection ∈ U.invtSubmodule := by
  rw [ordinaryProjection_def]
  exact (mem_invtSubmodule_iff_mapsTo _).mpr (LinearMap.mapsTo_ker_pow U _)

@[simp]
theorem ordinaryProjection_one : (1 : Module.End R M).ordinaryProjection = 1 :=
  one_pow _

@[simp]
theorem ordinaryProjection_zero : (0 : Module.End R M).ordinaryProjection = 0 :=
  zero_pow (factorial_ne_zero _)

/-- A submodule `A` with `A ≤ U(A)` is contained in the ordinary part. -/
theorem le_range_ordinaryProjection {U : Module.End R M} {A : Submodule R M} (hA : A ≤ A.map U) :
    A ≤ range U.ordinaryProjection := by
  have key : ∀ k, A ≤ A.map (U ^ k) := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih =>
      calc A ≤ A.map U := hA
        _ ≤ (A.map (U ^ k)).map U := Submodule.map_mono ih
        _ = A.map (U ^ (k + 1)) := by
          rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, _root_.pow_succ']
  rw [ordinaryProjection_def]
  exact (key _).trans LinearMap.map_le_range

variable [Finite M] {U : Module.End R M} {n : ℕ}

/-- The ordinary projector is the stable value of the factorial powers of `U`. -/
theorem ordinaryProjection_eq_pow_factorial (hn : Nat.card M ≤ n) :
    U.ordinaryProjection = U ^ n ! := by
  apply DFunLike.coe_injective
  rw [ordinaryProjection, FunLike.coe_pow_eq_iterate, FunLike.coe_pow_eq_iterate,
    iterate_factorial_eq_of_card_le le_rfl hn]

/-- The ordinary part of a finite module is the set of periodic points of `U`. -/
theorem coe_range_ordinaryProjection :
    (range U.ordinaryProjection : Set M) = periodicPts U := by
  rw [coe_range, ordinaryProjection, FunLike.coe_pow_eq_iterate,
    range_iterate_of_card_le (Nat.self_le_factorial _)]

theorem mem_range_ordinaryProjection_iff {x : M} :
    x ∈ range U.ordinaryProjection ↔ x ∈ periodicPts U := by
  rw [← SetLike.mem_coe, coe_range_ordinaryProjection]

/-- The ordinary projector fixes the `U`-periodic vectors. -/
theorem ordinaryProjection_apply_of_mem_periodicPts {x : M} (hx : x ∈ periodicPts U) :
    U.ordinaryProjection x = x := by
  rw [ordinaryProjection, pow_apply_eq_iterate]
  exact isPeriodicPt_factorial_of_card_le le_rfl hx

/-- The ordinary projector fixes its own values: `e_U (e_U x) = e_U x`. -/
@[simp]
theorem ordinaryProjection_ordinaryProjection_apply (x : M) :
    U.ordinaryProjection (U.ordinaryProjection x) = U.ordinaryProjection x :=
  ordinaryProjection_apply_of_mem_periodicPts <|
    mem_range_ordinaryProjection_iff.mp (mem_range_self _ x)

/-- On a finite module, the ordinary projector is idempotent: `e_U * e_U = e_U`. -/
theorem isIdempotentElem_ordinaryProjection : IsIdempotentElem U.ordinaryProjection :=
  LinearMap.ext ordinaryProjection_ordinaryProjection_apply

/-- The ordinary part is the image of `U ^ Nat.card M`. -/
theorem range_ordinaryProjection : range U.ordinaryProjection = range (U ^ Nat.card M) := by
  rw [← SetLike.coe_set_eq, coe_range_ordinaryProjection, coe_range, FunLike.coe_pow_eq_iterate,
    range_iterate_of_card_le le_rfl]

/-- The ordinary part is the intersection of the images of the powers of `U`. -/
theorem range_ordinaryProjection_eq_iInf :
    range U.ordinaryProjection = ⨅ k, range (U ^ k) := by
  refine le_antisymm (le_iInf fun k ↦ ?_) ?_
  · rw [ordinaryProjection_eq_pow_factorial (le_max_left (Nat.card M) k)]
    exact U.iterateRange.monotone ((le_max_right _ k).trans (Nat.self_le_factorial _))
  · exact iInf_le_of_le _ le_rfl

/-- The ordinary projector kills every vector killed by some power of `U`. -/
theorem ordinaryProjection_apply_eq_zero_of_pow_apply_eq_zero {x : M} {k : ℕ}
    (hx : (U ^ k) x = 0) : U.ordinaryProjection x = 0 := by
  rw [ordinaryProjection_eq_pow_factorial (le_max_left (Nat.card M) k)]
  exact pow_map_zero_of_le ((le_max_right _ k).trans (Nat.self_le_factorial _)) hx

/-- The non-ordinary part is the kernel of `U ^ Nat.card M`: on it, `U` is nilpotent with an
exponent bounded by the cardinality of `M`. -/
theorem ker_ordinaryProjection : ker U.ordinaryProjection = ker (U ^ Nat.card M) := by
  ext x
  refine ⟨fun hx ↦ ?_, ordinaryProjection_apply_eq_zero_of_pow_apply_eq_zero⟩
  have hper : (U ^ Nat.card M) x ∈ periodicPts U := by
    rw [pow_apply_eq_iterate]
    exact iterate_mem_periodicPts_of_card_le le_rfl x
  calc (U ^ Nat.card M) x = U.ordinaryProjection ((U ^ Nat.card M) x) :=
        (ordinaryProjection_apply_of_mem_periodicPts hper).symm
    _ = (U ^ Nat.card M) (U.ordinaryProjection x) := ordinaryProjection_pow_apply_comm U _ x
    _ = 0 := by rw [mem_ker.mp hx, map_zero]

theorem mem_ker_ordinaryProjection_iff {x : M} :
    x ∈ ker U.ordinaryProjection ↔ ∃ k, (U ^ k) x = 0 :=
  ⟨fun hx ↦ ⟨Nat.card M, mem_ker.mp ((ker_ordinaryProjection (U := U)).le hx)⟩,
    fun ⟨_, hk⟩ ↦ ordinaryProjection_apply_eq_zero_of_pow_apply_eq_zero hk⟩

/-- A submodule all of whose vectors are killed by some power of `U` is contained in the
non-ordinary part. -/
theorem le_ker_ordinaryProjection {B : Submodule R M} (hB : ∀ x ∈ B, ∃ k, (U ^ k) x = 0) :
    B ≤ ker U.ordinaryProjection :=
  fun x hx ↦ mem_ker_ordinaryProjection_iff.mpr (hB x hx)

/-- The non-ordinary part is the union of the kernels of the powers of `U`. -/
theorem ker_ordinaryProjection_eq_iSup :
    ker U.ordinaryProjection = ⨆ k, ker (U ^ k) := by
  refine le_antisymm ?_ (iSup_le fun k x hx ↦
    ordinaryProjection_apply_eq_zero_of_pow_apply_eq_zero (mem_ker.mp hx))
  rw [ker_ordinaryProjection]
  exact le_iSup (fun k ↦ ker (U ^ k)) _

/-- `U` restricts to a bijection of the ordinary part. -/
theorem bijOn_range_ordinaryProjection :
    Set.BijOn U (range U.ordinaryProjection) (range U.ordinaryProjection) := by
  rw [coe_range_ordinaryProjection]
  exact bijOn_periodicPts U

/-- On the ordinary part, the inverse of `U` is `U ^ ((Nat.card M)! - 1)`. -/
theorem invOn_range_ordinaryProjection :
    Set.InvOn (U ^ ((Nat.card M)! - 1)) U (range U.ordinaryProjection)
      (range U.ordinaryProjection) := by
  rw [coe_range_ordinaryProjection, FunLike.coe_pow_eq_iterate]
  exact invOn_iterate_factorial_pred le_rfl

/-- `U` restricted to the ordinary part, as a linear automorphism of it. Its inverse is the
restriction of `U ^ ((Nat.card M)! - 1)` (`coe_ordinaryEquiv_symm_apply`). -/
noncomputable def ordinaryEquiv (U : Module.End R M) :
    range U.ordinaryProjection ≃ₗ[R] range U.ordinaryProjection where
  toLinearMap := U.restrict U.range_ordinaryProjection_mem_invtSubmodule
  invFun x := ⟨(U ^ ((Nat.card M)! - 1)) x, by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact ⟨(U ^ ((Nat.card M)! - 1)) y, ordinaryProjection_pow_apply_comm U _ y⟩⟩
  left_inv x := Subtype.ext (invOn_range_ordinaryProjection.1 x.property)
  right_inv x := Subtype.ext (invOn_range_ordinaryProjection.2 x.property)

@[simp]
theorem coe_ordinaryEquiv_apply (x : range U.ordinaryProjection) :
    (U.ordinaryEquiv x : M) = U x :=
  (rfl)

@[simp]
theorem coe_ordinaryEquiv_symm_apply (x : range U.ordinaryProjection) :
    (U.ordinaryEquiv.symm x : M) = (U ^ ((Nat.card M)! - 1)) x :=
  (rfl)

/-- The ordinary projector is the identity exactly when `U` is invertible. -/
theorem ordinaryProjection_eq_one_iff : U.ordinaryProjection = 1 ↔ IsUnit U := by
  refine ⟨fun h ↦ .of_pow_eq_one h (factorial_ne_zero _), fun h ↦ LinearMap.ext fun x ↦ ?_⟩
  have hinj : Injective U := (Module.End.isUnit_iff U).mp h |>.injective
  exact ordinaryProjection_apply_of_mem_periodicPts (hinj.mem_periodicPts x)

/-- The ordinary projector vanishes exactly when `U` is nilpotent. -/
theorem ordinaryProjection_eq_zero_iff : U.ordinaryProjection = 0 ↔ IsNilpotent U := by
  refine ⟨fun h ↦ ⟨_, h⟩, fun ⟨k, hk⟩ ↦ LinearMap.ext fun x ↦ ?_⟩
  exact ordinaryProjection_apply_eq_zero_of_pow_apply_eq_zero (k := k) (by simp [hk])

variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Naturality of the ordinary projector: a linear map intertwining two endomorphisms of finite
modules intertwines their ordinary projectors. -/
theorem ordinaryProjection_comp_eq_comp_ordinaryProjection [Finite N] {U₁ : Module.End R M}
    {U₂ : Module.End R N} {f : M →ₗ[R] N} (h : U₂ ∘ₗ f = f ∘ₗ U₁) :
    U₂.ordinaryProjection ∘ₗ f = f ∘ₗ U₁.ordinaryProjection := by
  rw [ordinaryProjection_eq_pow_factorial (le_max_left (Nat.card M) (Nat.card N)),
    ordinaryProjection_eq_pow_factorial (le_max_right (Nat.card M) (Nat.card N))]
  exact commute_pow_left_of_commute h _

/-- Naturality of the ordinary projector, applied form: if `f` intertwines `U₁` and `U₂`, then
`e_{U₂} (f x) = f (e_{U₁} x)`. -/
theorem ordinaryProjection_apply_comm [Finite N] {U₁ : Module.End R M} {U₂ : Module.End R N}
    {f : M →ₗ[R] N} (h : U₂ ∘ₗ f = f ∘ₗ U₁) (x : M) :
    U₂.ordinaryProjection (f x) = f (U₁.ordinaryProjection x) :=
  LinearMap.congr_fun (ordinaryProjection_comp_eq_comp_ordinaryProjection h) x

/-- An intertwining map sends ordinary parts into ordinary parts. -/
theorem map_range_ordinaryProjection_le [Finite N] {U₁ : Module.End R M} {U₂ : Module.End R N}
    {f : M →ₗ[R] N} (h : U₂ ∘ₗ f = f ∘ₗ U₁) :
    (range U₁.ordinaryProjection).map f ≤ range U₂.ordinaryProjection := by
  rw [← range_comp, ← ordinaryProjection_comp_eq_comp_ordinaryProjection h]
  exact range_comp_le_range _ _

/-- An intertwining map sends non-ordinary parts into non-ordinary parts. -/
theorem map_ker_ordinaryProjection_le [Finite N] {U₁ : Module.End R M} {U₂ : Module.End R N}
    {f : M →ₗ[R] N} (h : U₂ ∘ₗ f = f ∘ₗ U₁) :
    (ker U₁.ordinaryProjection).map f ≤ ker U₂.ordinaryProjection := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_ker] at hx
  rw [mem_ker, ordinaryProjection_apply_comm h, hx, map_zero]

variable {U' : Module.End R N} {U'' : Module.End R P}

/-- Exactness of ordinary parts: for an exact sequence `N → M → P` with `f` intertwining `U'`
and `U`, the ordinary vectors of `M` killed by `g` are the images of ordinary vectors of `N`. -/
theorem map_range_ordinaryProjection_of_exact [Finite N] {f : N →ₗ[R] M} {g : M →ₗ[R] P}
    (hfg : Exact f g) (hf : U ∘ₗ f = f ∘ₗ U') :
    (range U'.ordinaryProjection).map f = ker g ⊓ range U.ordinaryProjection := by
  refine le_antisymm (le_inf ?_ (map_range_ordinaryProjection_le hf)) ?_
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact mem_ker.mpr (hfg.apply_apply_eq_zero _)
  · rintro x ⟨hxg, hxe⟩
    obtain ⟨y, rfl⟩ := (hfg x).mp (mem_ker.mp hxg)
    refine ⟨U'.ordinaryProjection y, mem_range_self _ y, ?_⟩
    rw [← ordinaryProjection_apply_comm hf,
      isIdempotentElem_ordinaryProjection.mem_range_iff.mp hxe]

/-- A surjection intertwining `U` and `U''` maps the ordinary part of `M` onto that of `P`. -/
theorem map_range_ordinaryProjection_of_surjective [Finite P] {g : M →ₗ[R] P} (hg : Surjective g)
    (h : U'' ∘ₗ g = g ∘ₗ U) :
    (range U.ordinaryProjection).map g = range U''.ordinaryProjection := by
  refine le_antisymm (map_range_ordinaryProjection_le h) ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨y, rfl⟩ := hg z
  exact ⟨U.ordinaryProjection y, mem_range_self _ y, (ordinaryProjection_apply_comm h y).symm⟩

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [Finite M] {U : Module.End R M}

/-- The ordinary projector is the projection onto `⨅ n, range (U ^ n)` along
`⨆ n, ker (U ^ n)` in the Fitting decomposition of `M` with respect to `U`. -/
theorem ordinaryProjection_eq_projection :
    U.ordinaryProjection = (⨅ n, range (U ^ n)).projection (⨆ n, ker (U ^ n))
      (isCompl_iSup_ker_pow_iInf_range_pow U).symm := by
  rw [isIdempotentElem_ordinaryProjection.ext_iff (Submodule.isIdempotentElem_projection _),
    Submodule.range_projection, Submodule.ker_projection]
  exact ⟨range_ordinaryProjection_eq_iInf, ker_ordinaryProjection_eq_iSup⟩

/-- Uniqueness of the ordinary decomposition, ordinary part: if `M = A ⊕ B` with `A ≤ U(A)` and
every vector of `B` killed by a power of `U`, then `A` is the ordinary part. -/
theorem range_ordinaryProjection_eq_of_isCompl {A B : Submodule R M} (hAB : IsCompl A B)
    (hA : A ≤ A.map U) (hB : ∀ x ∈ B, ∃ k, (U ^ k) x = 0) :
    range U.ordinaryProjection = A := by
  exact ((le_iff_eq_of_codisjoint_of_disjoint hAB.codisjoint
    (isIdempotentElem_ordinaryProjection.isCompl.disjoint.symm.mono_left
      (le_ker_ordinaryProjection hB))).mp
    (le_range_ordinaryProjection hA)).symm

/-- Uniqueness of the ordinary decomposition, non-ordinary part: if `M = A ⊕ B` with `A ≤ U(A)`
and every vector of `B` killed by a power of `U`, then `B` is the non-ordinary part. -/
theorem ker_ordinaryProjection_eq_of_isCompl {A B : Submodule R M} (hAB : IsCompl A B)
    (hA : A ≤ A.map U) (hB : ∀ x ∈ B, ∃ k, (U ^ k) x = 0) :
    ker U.ordinaryProjection = B := by
  exact ((le_iff_eq_of_codisjoint_of_disjoint hAB.symm.codisjoint
    (isIdempotentElem_ordinaryProjection.isCompl.disjoint.mono_left
      (le_range_ordinaryProjection hA))).mp (le_ker_ordinaryProjection hB)).symm

variable [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {U' : Module.End R N} {U'' : Module.End R P}

/-- Exactness of non-ordinary parts: for an exact sequence `N → M → P` with `f` intertwining `U'`
and `U`, the non-ordinary vectors of `M` killed by `g` are the images of non-ordinary vectors of
`N`. -/
theorem map_ker_ordinaryProjection_of_exact [Finite N] {f : N →ₗ[R] M} {g : M →ₗ[R] P}
    (hfg : Exact f g) (hf : U ∘ₗ f = f ∘ₗ U') :
    (ker U'.ordinaryProjection).map f = ker g ⊓ ker U.ordinaryProjection := by
  refine le_antisymm (le_inf ?_ (map_ker_ordinaryProjection_le hf)) ?_
  · rintro _ ⟨y, -, rfl⟩
    exact mem_ker.mpr (hfg.apply_apply_eq_zero _)
  · rintro x ⟨hxg, hxe⟩
    obtain ⟨y, rfl⟩ := (hfg x).mp (mem_ker.mp hxg)
    refine ⟨(1 - U'.ordinaryProjection) y,
      isIdempotentElem_ordinaryProjection.ker_eq_range_one_sub.ge (mem_range_self _ y), ?_⟩
    simp [← ordinaryProjection_apply_comm hf, mem_ker.mp hxe]

/-- A surjection intertwining `U` and `U''` maps the non-ordinary part of `M` onto that of `P`. -/
theorem map_ker_ordinaryProjection_of_surjective [Finite P] {g : M →ₗ[R] P} (hg : Surjective g)
    (h : U'' ∘ₗ g = g ∘ₗ U) :
    (ker U.ordinaryProjection).map g = ker U''.ordinaryProjection := by
  refine le_antisymm (map_ker_ordinaryProjection_le h) fun z hz ↦ ?_
  obtain ⟨y, rfl⟩ := hg z
  refine ⟨(1 - U.ordinaryProjection) y,
    isIdempotentElem_ordinaryProjection.ker_eq_range_one_sub.ge (mem_range_self _ y), ?_⟩
  simp [← ordinaryProjection_apply_comm h, mem_ker.mp hz]

/-- The ordinary part of the quotient of `M` by a `U`-stable submodule `Q` is the image of the
ordinary part of `M`. -/
theorem range_ordinaryProjection_mapQ (Q : Submodule R M) (hQ : Q ≤ Q.comap U) :
    range (ordinaryProjection (Q.mapQ Q U hQ)) = (range U.ordinaryProjection).map Q.mkQ := by
  have : Finite (M ⧸ Q) := _root_.Finite.of_surjective _ Q.mkQ_surjective
  exact (map_range_ordinaryProjection_of_surjective Q.mkQ_surjective (Q.mapQ_mkQ Q U)).symm

/-- The non-ordinary part of the quotient of `M` by a `U`-stable submodule `Q` is the image of
the non-ordinary part of `M`. -/
theorem ker_ordinaryProjection_mapQ (Q : Submodule R M) (hQ : Q ≤ Q.comap U) :
    ker (ordinaryProjection (Q.mapQ Q U hQ)) = (ker U.ordinaryProjection).map Q.mkQ := by
  have : Finite (M ⧸ Q) := _root_.Finite.of_surjective _ Q.mkQ_surjective
  exact (map_ker_ordinaryProjection_of_surjective Q.mkQ_surjective (Q.mapQ_mkQ Q U)).symm

end Ring

end Module.End
