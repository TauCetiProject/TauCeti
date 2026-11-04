/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Topology

/-!
# Completion of a module along a decreasing family of submodules

Let `J₀ ⊇ J₁ ⊇ J₂ ⊇ ⋯` be a decreasing family of submodules of a module `M` over a ring `R`, which
need not be commutative. The quotients `M ⧸ J₀ ← M ⧸ J₁ ← M ⧸ J₂ ← ⋯`, with the quotient maps
`Submodule.factor` as transitions, form a tower (`TauCeti.ModuleTower.quotients`). Its limit,
with the inverse limit topology of `TauCeti.Algebra.Category.ModuleCat.Tower.Topology`, is the
completion of `M` for the linear topology in which the `Jₙ` form a basis of neighbourhoods of
zero.

The canonical map `M → lim M ⧸ Jₙ` (`TauCeti.ModuleTower.toLimQuotients`) sends `x` to the family
of its classes. Its kernel is the intersection of the `Jₙ`, so it is injective exactly when this
topology on `M` is Hausdorff; the preimage of the kernel of the `n`-th projection is `Jₙ`, so the
topology induced on `M` is the `J`-topology; and its range is dense. The projections of the limit
are surjective, since the transitions are.

The completion is functorial for maps which are continuous for these linear topologies. A
semilinear map `f : M → N` such that every `J'ₙ` contains the image of some `Jₘ` induces a
continuous semilinear map `lim M ⧸ Jₙ → lim N ⧸ J'ₙ` (`TauCeti.ModuleTower.limQuotientsMap`),
whose `n`-th coordinate is the class of `f b` for any representative `b` of such an `m`-th
coordinate. It extends `f`, it is the only continuous map extending `f`, and it is compatible with
identities and composition.

The ideal-power filtrations `Iⁿ⁺¹ M` of a commutative ring are handled by the dedicated tower
`TauCeti.ModuleTower.reduction`, whose limit is Mathlib's `AdicCompletion`. The present
construction allows arbitrary decreasing families over noncommutative rings, such as the left
ideals of high-order currents in an enveloping algebra of an affine Lie algebra at a fixed level.

## Main definitions

* `TauCeti.ModuleTower.quotients`: the tower of quotients `M ⧸ Jₙ`.
* `TauCeti.ModuleTower.quotientsπ`: the quotient maps `M → M ⧸ Jₙ`.
* `TauCeti.ModuleTower.toLimQuotients`: the canonical map `M → lim M ⧸ Jₙ`.
* `TauCeti.ModuleTower.limQuotientsMap`: the map of completions induced by a continuous
  semilinear map.

## Main results

* `TauCeti.ModuleTower.limπ_quotients_surjective`: the projections of the limit are surjective.
* `TauCeti.ModuleTower.ker_toLimQuotients`: the kernel of the canonical map is `⨅ n, Jₙ`.
* `TauCeti.ModuleTower.comap_toLimQuotients_ker_limπ`: the canonical map pulls the kernel of the
  `n`-th projection back to `Jₙ`.
* `TauCeti.ModuleTower.denseRange_toLimQuotients`: the canonical map has dense range.
* `TauCeti.ModuleTower.limπ_limQuotientsMap`, `TauCeti.ModuleTower.eq_limQuotientsMap`: the
  coordinates of the induced map, and its uniqueness among continuous extensions of `f`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, for completions of modules for linear
  topologies.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  (J : ℕ → Submodule R M) (hJ : Antitone J)

/-- The tower `M ⧸ J₀ ← M ⧸ J₁ ← M ⧸ J₂ ← ⋯` of quotients of a module `M` by a decreasing family
of submodules `Jₙ`, with the quotient maps as transitions. Its terms are handled through the
quotient maps `ModuleTower.quotientsπ`. -/
def quotients : ModuleTower.{v} R where
  obj n := ModuleCat.of R (M ⧸ J n.unop)
  map f := ModuleCat.ofHom (Submodule.factor (hJ (leOfHom f.unop)))
  -- The composites of quotient maps are quotient maps, by definition of `Submodule.factor`.
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The `n`-th term of the tower of quotients is `M ⧸ Jₙ`. -/
theorem quotients_obj (n : ℕ) : (quotients J hJ).obj (op n) = ModuleCat.of R (M ⧸ J n) :=
  (rfl)

/-- The quotient map from `M` onto the `n`-th term `M ⧸ Jₙ` of the tower of quotients. -/
def quotientsπ (n : ℕ) : M →ₗ[R] (quotients J hJ).obj (op n) :=
  (J n).mkQ

theorem quotientsπ_surjective (n : ℕ) : Function.Surjective (quotientsπ J hJ n) :=
  Submodule.mkQ_surjective _

@[simp]
theorem ker_quotientsπ (n : ℕ) : LinearMap.ker (quotientsπ J hJ n) = J n :=
  Submodule.ker_mkQ _

@[simp]
theorem quotientsπ_eq_zero_iff {n : ℕ} {x : M} : quotientsπ J hJ n x = 0 ↔ x ∈ J n := by
  rw [← LinearMap.mem_ker, ker_quotientsπ]

@[simp]
theorem transitionOfLE_quotientsπ {n k : ℕ} (h : n ≤ k) (x : M) :
    (quotients J hJ).transitionOfLE h (quotientsπ J hJ k x) = quotientsπ J hJ n x := by
  -- The transitions of `quotients` are the quotient maps `Submodule.factor`, by definition.
  rw [transitionOfLE_def]
  rfl

@[simp]
theorem transitionOfLE_comp_quotientsπ {n k : ℕ} (h : n ≤ k) :
    (quotients J hJ).transitionOfLE h ∘ₗ quotientsπ J hJ k = quotientsπ J hJ n :=
  LinearMap.ext (transitionOfLE_quotientsπ J hJ h)

@[simp]
theorem transition_comp_quotientsπ (n : ℕ) :
    (quotients J hJ).transition n ∘ₗ quotientsπ J hJ (n + 1) = quotientsπ J hJ n := by
  rw [← transitionOfLE_succ, transitionOfLE_comp_quotientsπ]

@[simp]
theorem transition_quotientsπ (n : ℕ) (x : M) :
    (quotients J hJ).transition n (quotientsπ J hJ (n + 1) x) = quotientsπ J hJ n x :=
  LinearMap.congr_fun (transition_comp_quotientsπ J hJ n) x

/-- The transitions of the tower of quotients are surjective. -/
theorem transition_quotients_surjective (n : ℕ) :
    Function.Surjective ((quotients J hJ).transition n) := by
  rw [transition_def]
  exact Submodule.factor_surjective (hJ (Nat.le_succ n))

/-- The projections `lim M ⧸ Jₖ → M ⧸ Jₙ` of the limit of the tower of quotients are
surjective. -/
theorem limπ_quotients_surjective (n : ℕ) : Function.Surjective ((quotients J hJ).limπ n) :=
  limπ_surjective _ (transition_quotients_surjective J hJ) n

/-- The canonical map `M → lim M ⧸ Jₙ`, sending `x` to the family of its classes. -/
def toLimQuotients : M →ₗ[R] (quotients J hJ).lim :=
  (quotients J hJ).limLift (quotientsπ J hJ) (transition_comp_quotientsπ J hJ)

@[simp]
theorem limπ_comp_toLimQuotients (n : ℕ) :
    (quotients J hJ).limπ n ∘ₗ toLimQuotients J hJ = quotientsπ J hJ n := by
  rw [toLimQuotients, limπ_comp_limLift]

@[simp]
theorem coe_toLimQuotients_apply (x : M) (n : ℕ) :
    (toLimQuotients J hJ x : (quotients J hJ).Product) n = quotientsπ J hJ n x := by
  rw [← limπ_apply, ← LinearMap.comp_apply, limπ_comp_toLimQuotients]

/-- The canonical map pulls the kernel of the `n`-th projection back to `Jₙ`: the topology which
the limit induces on `M` is the linear topology defined by the `Jₙ`. -/
@[simp]
theorem comap_toLimQuotients_ker_limπ (n : ℕ) :
    (LinearMap.ker ((quotients J hJ).limπ n)).comap (toLimQuotients J hJ) = J n := by
  rw [← LinearMap.ker_comp, limπ_comp_toLimQuotients, ker_quotientsπ]

/-- The kernel of the canonical map `M → lim M ⧸ Jₙ` is the intersection of the `Jₙ`. -/
@[simp]
theorem ker_toLimQuotients : LinearMap.ker (toLimQuotients J hJ) = ⨅ n, J n := by
  simp only [toLimQuotients, ker_limLift, ker_quotientsπ]

/-- The canonical map `M → lim M ⧸ Jₙ` is injective exactly when the `Jₙ` intersect to zero. -/
theorem toLimQuotients_injective_iff :
    Function.Injective (toLimQuotients J hJ) ↔ ⨅ n, J n = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ker_toLimQuotients]

/-- The canonical map `M → lim M ⧸ Jₙ` has dense range. -/
theorem denseRange_toLimQuotients : DenseRange (toLimQuotients J hJ) :=
  denseRange_iff.mpr fun x n ↦ by
    obtain ⟨y, hy⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n x)
    exact ⟨y, by rw [limπ_apply, coe_toLimQuotients_apply, hy]⟩

variable {J hJ} in
/-- A representative of the `k`-th coordinate of a point of `lim M ⧸ Jₙ` also represents its
`n`-th coordinate for `n ≤ k`. -/
theorem quotientsπ_eq_limπ_of_le {x : (quotients J hJ).lim} {n k : ℕ} (h : n ≤ k) {b : M}
    (hb : quotientsπ J hJ k b = (quotients J hJ).limπ k x) :
    quotientsπ J hJ n b = (quotients J hJ).limπ n x := by
  rw [← transitionOfLE_quotientsπ J hJ h, hb, ← LinearMap.comp_apply, transitionOfLE_comp_limπ]

/-! ### Functoriality -/

section Map

variable {J hJ} {S : Type*} [Ring S] {τ : R →+* S} {N : Type*} [AddCommGroup N] [Module S N]
  {J' : ℕ → Submodule S N} {hJ' : Antitone J'} (f : M →ₛₗ[τ] N)

/-- If `b` and `b'` represent the `m`-th and `m'`-th coordinates of a point of `lim M ⧸ Jₖ`, and
`f` carries both `Jₘ` and `Jₘ'` into `J'ₙ`, then `f b` and `f b'` have the same class modulo
`J'ₙ`. -/
private theorem quotientsπ_eq_quotientsπ_of_limπ_eq {x : (quotients J hJ).lim} {n m m' : ℕ}
    (hm : J m ≤ (J' n).comap f) (hm' : J m' ≤ (J' n).comap f) {b b' : M}
    (hb : quotientsπ J hJ m b = (quotients J hJ).limπ m x)
    (hb' : quotientsπ J hJ m' b' = (quotients J hJ).limπ m' x) :
    quotientsπ J' hJ' n (f b) = quotientsπ J' hJ' n (f b') := by
  -- Both are the class of `f c` for a representative `c` at the common refinement `max m m'`.
  obtain ⟨c, hc⟩ := quotientsπ_surjective J hJ _ ((quotients J hJ).limπ (max m m') x)
  have key {p : ℕ} (hp : J p ≤ (J' n).comap f) (hpm : p ≤ max m m') {d : M}
      (hd : quotientsπ J hJ p d = (quotients J hJ).limπ p x) :
      quotientsπ J' hJ' n (f d) = quotientsπ J' hJ' n (f c) := by
    have h := hd.trans (quotientsπ_eq_limπ_of_le hpm hc).symm
    rw [← sub_eq_zero, ← map_sub, quotientsπ_eq_zero_iff] at h ⊢
    rw [← map_sub]
    exact hp h
  exact (key hm (le_max_left m m') hb).trans (key hm' (le_max_right m m') hb').symm

variable (hJ hJ')

/-- The map `M ⧸ Jₘ → N ⧸ J'ₙ` induced by `f`, between terms of the towers of quotients. -/
private def quotientsMapQ {m n : ℕ} (h : J m ≤ (J' n).comap f) :
    (quotients J hJ).obj (op m) →ₛₗ[τ] (quotients J' hJ').obj (op n) :=
  (J m).mapQ (J' n) f h

private theorem quotientsMapQ_quotientsπ {m n : ℕ} (h : J m ≤ (J' n).comap f) (b : M) :
    quotientsMapQ hJ hJ' f h (quotientsπ J hJ m b) = quotientsπ J' hJ' n (f b) :=
  -- `quotientsπ` is the quotient map `Submodule.mkQ`, on which `Submodule.mapQ` is `f`.
  (rfl)

variable (hf : ∀ n, ∃ m, J m ≤ (J' n).comap f)

/-- The `n`-th coordinate of `TauCeti.ModuleTower.limQuotientsMap`, computed at the order chosen
by `hf`. -/
private def limQuotientsMapCoord (n : ℕ) :
    (quotients J hJ).lim →ₛₗ[τ] (quotients J' hJ').obj (op n) :=
  quotientsMapQ hJ hJ' f (hf n).choose_spec ∘ₛₗ (quotients J hJ).limπ (hf n).choose

private theorem limQuotientsMapCoord_eq {x : (quotients J hJ).lim} {n m : ℕ}
    (hm : J m ≤ (J' n).comap f) {b : M} (hb : quotientsπ J hJ m b = (quotients J hJ).limπ m x) :
    limQuotientsMapCoord hJ hJ' f hf n x = quotientsπ J' hJ' n (f b) := by
  obtain ⟨c, hc⟩ := quotientsπ_surjective J hJ _ ((quotients J hJ).limπ (hf n).choose x)
  rw [limQuotientsMapCoord, LinearMap.comp_apply, ← hc, quotientsMapQ_quotientsπ]
  exact quotientsπ_eq_quotientsπ_of_limπ_eq f (hf n).choose_spec hm hc hb

/-- **Functoriality of the completion.** A semilinear map `f : M → N` which is continuous for the
linear topologies, in that for every `n` it carries some `Jₘ` into `J'ₙ`, induces a semilinear map
`lim M ⧸ Jₙ → lim N ⧸ J'ₙ`. The `n`-th coordinate of the image of a point is the class of `f b`
for any representative `b` of an `m`-th coordinate of the point with `f (Jₘ) ⊆ J'ₙ`
(`TauCeti.ModuleTower.limπ_limQuotientsMap`). -/
def limQuotientsMap : (quotients J hJ).lim →ₛₗ[τ] (quotients J' hJ').lim where
  toFun x := ⟨fun n ↦ limQuotientsMapCoord hJ hJ' f hf n x, (quotients J' hJ').mem_lim.2 fun n ↦ by
    obtain ⟨c, hc⟩ := quotientsπ_surjective J hJ _
      ((quotients J hJ).limπ (max (hf n).choose (hf (n + 1)).choose) x)
    rw [limQuotientsMapCoord_eq hJ hJ' f hf (hf (n + 1)).choose_spec
        (quotientsπ_eq_limπ_of_le (le_max_right _ _) hc),
      limQuotientsMapCoord_eq hJ hJ' f hf (hf n).choose_spec
        (quotientsπ_eq_limπ_of_le (le_max_left _ _) hc), transition_quotientsπ]⟩
  map_add' x y := Subtype.ext <| funext fun n ↦
    map_add (limQuotientsMapCoord hJ hJ' f hf n) x y
  map_smul' r x := Subtype.ext <| funext fun n ↦
    map_smulₛₗ (limQuotientsMapCoord hJ hJ' f hf n) r x

/-- The coordinates of the induced map: the `n`-th coordinate of the image of `x` is the class of
`f b`, for any representative `b` of the `m`-th coordinate of `x` with `f (Jₘ) ⊆ J'ₙ`. -/
theorem limπ_limQuotientsMap {x : (quotients J hJ).lim} {n m : ℕ} (hm : J m ≤ (J' n).comap f)
    {b : M} (hb : quotientsπ J hJ m b = (quotients J hJ).limπ m x) :
    (quotients J' hJ').limπ n (limQuotientsMap hJ hJ' f hf x) = quotientsπ J' hJ' n (f b) := by
  rw [limπ_apply]
  exact limQuotientsMapCoord_eq hJ hJ' f hf hm hb

/-- The induced map extends `f`. -/
@[simp]
theorem limQuotientsMap_toLimQuotients (b : M) :
    limQuotientsMap hJ hJ' f hf (toLimQuotients J hJ b) = toLimQuotients J' hJ' (f b) :=
  lim_ext _ fun n ↦ by
    obtain ⟨m, hm⟩ := hf n
    rw [limπ_limQuotientsMap hJ hJ' f hf hm (by rw [limπ_apply, coe_toLimQuotients_apply]),
      limπ_apply, coe_toLimQuotients_apply]

/-- The induced map is continuous for the inverse limit topologies. -/
theorem continuous_limQuotientsMap : Continuous (limQuotientsMap hJ hJ' f hf) := by
  refine continuous_of_tendsto_nhds_zero (limQuotientsMap hJ hJ' f hf)
    (((quotients J hJ).hasBasis_nhds_zero.tendsto_iff
      (quotients J' hJ').hasBasis_nhds_zero).2 fun n _ ↦ ?_)
  obtain ⟨m, hm⟩ := hf n
  refine ⟨m, trivial, fun x hx ↦ ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
  rw [limπ_limQuotientsMap hJ hJ' f hf hm (b := 0) (by rw [map_zero, hx]), map_zero, map_zero]

/-- **Uniqueness of the induced map.** A continuous map `lim M ⧸ Jₙ → lim N ⧸ J'ₙ` extending `f`
is `TauCeti.ModuleTower.limQuotientsMap hJ hJ' f hf`. -/
theorem eq_limQuotientsMap {φ : (quotients J hJ).lim → (quotients J' hJ').lim} (hφ : Continuous φ)
    (h : ∀ b, φ (toLimQuotients J hJ b) = toLimQuotients J' hJ' (f b)) :
    φ = limQuotientsMap hJ hJ' f hf :=
  (denseRange_toLimQuotients J hJ).equalizer hφ (continuous_limQuotientsMap hJ hJ' f hf)
    (funext fun b ↦ (h b).trans (limQuotientsMap_toLimQuotients hJ hJ' f hf b).symm)

/-- The identity induces the identity. -/
@[simp]
theorem limQuotientsMap_id (h : ∀ n, ∃ m, J m ≤ (J n).comap LinearMap.id) :
    limQuotientsMap hJ hJ LinearMap.id h = LinearMap.id :=
  LinearMap.ext <| congrFun <|
    (eq_limQuotientsMap hJ hJ LinearMap.id h continuous_id fun _ ↦ rfl).symm

/-- The map induced by a composite is the composite of the induced maps. -/
theorem limQuotientsMap_comp {T : Type*} [Ring T] {τ' : S →+* T} {τ'' : R →+* T}
    [RingHomCompTriple τ τ' τ''] {P : Type*} [AddCommGroup P] [Module T P]
    {J'' : ℕ → Submodule T P} (hJ'' : Antitone J'') (g : N →ₛₗ[τ'] P)
    (hg : ∀ n, ∃ m, J' m ≤ (J'' n).comap g) (hgf : ∀ n, ∃ m, J m ≤ (J'' n).comap (g ∘ₛₗ f)) :
    limQuotientsMap hJ hJ'' (g ∘ₛₗ f) hgf =
      limQuotientsMap hJ' hJ'' g hg ∘ₛₗ limQuotientsMap hJ hJ' f hf := by
  ext x : 1
  refine lim_ext _ fun n ↦ ?_
  obtain ⟨p, hp⟩ := hg n
  obtain ⟨m, hm⟩ := hf p
  obtain ⟨b, hb⟩ := quotientsπ_surjective J hJ m ((quotients J hJ).limπ m x)
  rw [LinearMap.comp_apply, limπ_limQuotientsMap hJ hJ'' _ hgf (fun c hc ↦ hp (hm hc)) hb,
    limπ_limQuotientsMap hJ' hJ'' g hg hp (limπ_limQuotientsMap hJ hJ' f hf hm hb).symm,
    LinearMap.comp_apply]

end Map

end TauCeti.ModuleTower
