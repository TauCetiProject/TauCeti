/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.LinearAlgebra.Pi
import TauCeti.Order.Filter.Cofinite.Basic

/-!
# Gaps in Mathlib's `ZeroAtFilter` / `BoundedAtFilter` API

Mathlib's `Filter.ZeroAtFilter` and `Filter.BoundedAtFilter` are closed under binary sums
(`Filter.ZeroAtFilter.add`, `Filter.BoundedAtFilter.add`), and the bounded functions are closed
under a `Finset.prod` (`Filter.BoundedAtFilter.prod`, via `boundedFilterSubalgebra`). The additive
counterpart of that product lemma is not recorded upstream; this file adds it for both predicates.

The gap shows up wherever an operator is a finite sum of slashes: proving that such an operator
stays bounded, or stays vanishing, along `atImInfty` is an induction over the summands, and
without these each call site reruns it.

Mathlib also has no rule for pushing a vanishing function through a map. `ZeroAtFilter` is
convergence to `0`, so only the behaviour of that map **at `0`** matters — global continuity is
not needed, and asking for it would exclude the topological modules that carry `ContinuousAdd`
rather than `IsTopologicalAddGroup`.

Functions vanishing along a filter also form an additive subgroup when their target has
continuous negation. The subgroup below uses exactly the carrier of Mathlib's
`Filter.zeroAtFilterAddSubmonoid` and `Filter.zeroAtFilterSubmodule`; it supplies additive
inverses independently of any scalar ring.

Along `Filter.cofinite`, functions vanishing into a `T1Space` with countably generated
neighbourhoods of `0` have countable support (`Filter.ZeroAtFilter.countable_support`), and
`Filter.zeroAtFilterSubmodule` supports pullback (`Filter.zeroAtFilterComap`), reindexing
(`Filter.zeroAtFilterCofiniteCongr`), extension by zero (`Filter.zeroAtFilterExtend`), and
retractions from countable indices into `ℕ` (`Filter.exists_retract_zeroAtFilterSubmodule_nat`).

## Main results

* `Filter.zeroAtFilterAddSubgroup`: the additive subgroup of functions vanishing along a filter.
* `Filter.ZeroAtFilter.sum`: a finite sum of functions vanishing along `l` vanishes along `l`.
* `Filter.BoundedAtFilter.sum`: a finite sum of functions bounded along `l` is bounded along `l`.
* `Filter.ZeroAtFilter.comp`: a function vanishing along `l`, composed with a zero-preserving map
  continuous at `0`, still vanishes along `l`.
* `Filter.ZeroAtFilter.countable_support`: a family vanishing along `cofinite` into a `T1Space`
  with countably generated neighbourhoods of `0` has countable support.
* `Filter.zeroAtFilterComap`, `Filter.zeroAtFilterCofiniteCongr`, and `Filter.zeroAtFilterExtend`:
  pullback, reindexing equivalence, and extension by zero on `Filter.zeroAtFilterSubmodule`.
* `Filter.exists_retract_zeroAtFilterSubmodule_nat`: for countable `ι`, `c₀(ι, M)` is a linear
  retract of `c₀(ℕ, M)`.

## Provenance

No code is transcribed. The gap was identified while porting the cusp chain of the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0),
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`: its `heckeT_p_ut_zero_at_cusps` (lines 62-70)
open-codes precisely this induction with `Finset.sum_induction`, which is also the proof plan
`BoundedAtFilter.sum` follows below. The statements here are about Mathlib's
`Filter.ZeroAtFilter` / `Filter.BoundedAtFilter` at an arbitrary filter and index type, not about
modular forms.
-/

public section

open Finset
open scoped Topology

namespace Filter

variable {α β ι : Type*} {l : Filter α} {s : Finset ι} {f : ι → α → β}

/-- The additive subgroup of functions tending to zero along a filter. Its additive submonoid
is `zeroAtFilterAddSubmonoid`, so it also has the carrier of `zeroAtFilterSubmodule` without
requiring ring scalars. -/
def zeroAtFilterAddSubgroup [TopologicalSpace β] [AddGroup β] [ContinuousAdd β]
    [ContinuousNeg β] (l : Filter α) : AddSubgroup (α → β) where
  toAddSubmonoid := zeroAtFilterAddSubmonoid l
  neg_mem' := ZeroAtFilter.neg

@[simp]
theorem mem_zeroAtFilterAddSubgroup [TopologicalSpace β] [AddGroup β] [ContinuousAdd β]
    [ContinuousNeg β] {f : α → β} : f ∈ zeroAtFilterAddSubgroup l ↔ ZeroAtFilter l f := (Iff.rfl)

@[simp]
theorem zeroAtFilterAddSubgroup_toAddSubmonoid [TopologicalSpace β] [AddGroup β]
    [ContinuousAdd β] [ContinuousNeg β] (l : Filter α) :
    (zeroAtFilterAddSubgroup (β := β) l).toAddSubmonoid = zeroAtFilterAddSubmonoid l := (rfl)

/-- **A finite sum of functions vanishing along `l` vanishes along `l`.** The additive companion
of `Filter.BoundedAtFilter.prod`. The `AddCommMonoid` hypothesis is what `Finset.sum` requires. -/
theorem ZeroAtFilter.sum [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    (h : ∀ i ∈ s, ZeroAtFilter l (f i)) : ZeroAtFilter l (∑ i ∈ s, f i) :=
  sum_mem (S := zeroAtFilterAddSubmonoid l) h

/-- **A finite sum of functions bounded along `l` is bounded along `l`** — the additive companion
of `Filter.BoundedAtFilter.prod`. -/
theorem BoundedAtFilter.sum [SeminormedAddCommGroup β]
    (h : ∀ i ∈ s, BoundedAtFilter l (f i)) : BoundedAtFilter l (∑ i ∈ s, f i) :=
  Finset.sum_induction f (BoundedAtFilter l) (fun _ _ ↦ BoundedAtFilter.add)
    (const_boundedAtFilter l 0) h

/-- **A vanishing function stays vanishing under a zero-preserving map continuous at `0`.**

Only continuity **at `0`** is asked for. `ZeroAtFilter` is convergence to `0`, so nothing about
`φ` away from `0` is involved; requiring `Continuous φ` would be strictly stronger, and for a
linear map the two coincide only when the topology is translation-invariant. -/
theorem ZeroAtFilter.comp {γ : Type*} [Zero β] [TopologicalSpace β] [Zero γ] [TopologicalSpace γ]
    {g : α → β} {φ : β → γ} (hg : ZeroAtFilter l g) (hφ : ContinuousAt φ 0) (h0 : φ 0 = 0) :
    ZeroAtFilter l (φ ∘ g) := by
  have h := Filter.Tendsto.comp hφ hg
  rwa [h0] at h

/-- **Zeroing values keeps a function zero at a filter.** If `g` eventually agrees with `f` or
vanishes, then `g` inherits `ZeroAtFilter`: since `0` lies in every neighbourhood of `0`, the
preimage of such a neighbourhood under `g` contains the intersection of the one under `f` with
the set where the hypothesis holds.

Only an eventual hypothesis is needed, because convergence along `l` sees `g` only through sets
in `l`. Stated pointwise rather than for an indicator, so it carries no decidability hypothesis
and also covers truncations that are not indicators. -/
theorem ZeroAtFilter.of_eventually_eq_or_eq_zero [Zero β] [TopologicalSpace β] {f g : α → β}
    (hf : ZeroAtFilter l f) (h : ∀ᶠ a in l, g a = f a ∨ g a = 0) : ZeroAtFilter l g := fun _ hU ↦
  Filter.mem_map.mpr (Filter.mem_of_superset
    (Filter.inter_mem (Filter.mem_map.mp (hf hU)) h) fun a ha ↦ by
      rcases ha.2 with he | he
      · simpa [he] using ha.1
      · simpa [he] using mem_of_mem_nhds hU)

/-- A family tending to zero along `Filter.cofinite` into a `T1Space` with countably generated
neighbourhoods of `0` has countable support. -/
theorem ZeroAtFilter.countable_support [Zero β] [TopologicalSpace β] [T1Space β]
    [(𝓝 (0 : β)).IsCountablyGenerated] {g : α → β} (hg : ZeroAtFilter cofinite g) :
    (Function.support g).Countable := by
  have h := hg.countable_compl_preimage_ker; rw [ker_nhds] at h; exact h.mono fun _ hx ↦ hx

section SubmoduleMaps

variable (A M : Type*) [Semiring A] [AddCommMonoid M] [TopologicalSpace M]
  [Module A M] [ContinuousAdd M] [ContinuousConstSMul A M]

/-- Precomposition along `j : κ → ι` tending from `l₁` to `l₂` pulls `M`-valued functions vanishing
along `l₂` back to functions vanishing along `l₁`. -/
def zeroAtFilterComap {κ ι : Type*} {l₁ : Filter κ} {l₂ : Filter ι} {j : κ → ι}
    (hj : Tendsto j l₁ l₂) :
    zeroAtFilterSubmodule (β := M) A l₂ →ₗ[A] zeroAtFilterSubmodule (β := M) A l₁ where
  toFun g := ⟨(g : ι → M) ∘ j, Tendsto.comp g.2 hj⟩
  map_add' _ _ := rfl; map_smul' _ _ := rfl

variable {A M} in
/-- The underlying function of `zeroAtFilterComap` is precomposition with `j`. -/
@[simp]
theorem coe_zeroAtFilterComap {κ ι : Type*} {l₁ : Filter κ} {l₂ : Filter ι} {j : κ → ι}
    (hj : Tendsto j l₁ l₂) (g : zeroAtFilterSubmodule (β := M) A l₂) :
    (zeroAtFilterComap A M hj g : κ → M) = (g : ι → M) ∘ j := (rfl)

/-- Pullback of vanishing functions is contravariantly functorial in the map. -/
theorem zeroAtFilterComap_comp {κ ι γ : Type*} {l₁ : Filter κ} {l₂ : Filter ι} {l₃ : Filter γ}
    {j₁ : κ → ι} {j₂ : ι → γ} (hj₁ : Tendsto j₁ l₁ l₂) (hj₂ : Tendsto j₂ l₂ l₃) :
    zeroAtFilterComap A M hj₁ ∘ₗ zeroAtFilterComap A M hj₂ =
      zeroAtFilterComap A M (hj₂.comp hj₁) := (rfl)

/-- Reindexing along an equivalence `e : ι ≃ κ` identifies the `A`-modules of `M`-valued null
families along `Filter.cofinite`. -/
def zeroAtFilterCofiniteCongr {ι κ : Type*} (e : ι ≃ κ) :
    zeroAtFilterSubmodule (β := M) A (cofinite : Filter ι) ≃ₗ[A]
      zeroAtFilterSubmodule (β := M) A (cofinite : Filter κ) :=
  LinearEquiv.ofLinearMap (zeroAtFilterComap A M e.symm.injective.tendsto_cofinite)
    (zeroAtFilterComap A M e.injective.tendsto_cofinite)
    (LinearMap.ext fun g ↦ Subtype.ext <| funext fun k ↦ congrArg g.1 (e.apply_symm_apply k))
    (LinearMap.ext fun f ↦ Subtype.ext <| funext fun i ↦ congrArg f.1 (e.symm_apply_apply i))

variable {A M} in
/-- Applying `zeroAtFilterCofiniteCongr` evaluates at `e.symm k`. -/
@[simp]
theorem coe_zeroAtFilterCofiniteCongr_apply {ι κ : Type*} (e : ι ≃ κ)
    (f : zeroAtFilterSubmodule (β := M) A (cofinite : Filter ι)) (k : κ) :
    (zeroAtFilterCofiniteCongr A M e f : κ → M) k = (f : ι → M) (e.symm k) := (rfl)

variable {A M} in
/-- Applying `(zeroAtFilterCofiniteCongr A M e).symm` evaluates at `e i`. -/
@[simp]
theorem coe_zeroAtFilterCofiniteCongr_symm_apply {ι κ : Type*} (e : ι ≃ κ)
    (g : zeroAtFilterSubmodule (β := M) A (cofinite : Filter κ)) (i : ι) :
    ((zeroAtFilterCofiniteCongr A M e).symm g : ι → M) i = (g : κ → M) (e i) := (rfl)

/-- Extending a null family along `j : κ → ι` by `0` outside the range of `j` yields a null family
along `Filter.cofinite`. -/
noncomputable def zeroAtFilterExtend {κ ι : Type*} (j : κ → ι) :
    zeroAtFilterSubmodule (β := M) A (cofinite : Filter κ) →ₗ[A]
      zeroAtFilterSubmodule (β := M) A (cofinite : Filter ι) :=
  ((Function.ExtendByZero.linearMap A M j).comp
    (zeroAtFilterSubmodule (β := M) A cofinite).subtype).codRestrict _ fun f ↦
      f.2.extend_cofinite j (pure_le_nhds 0)

variable {A M} in
/-- The underlying function of `zeroAtFilterExtend` is `Function.extend` by `0`. -/
@[simp]
theorem coe_zeroAtFilterExtend {κ ι : Type*} (j : κ → ι)
    (f : zeroAtFilterSubmodule (β := M) A (cofinite : Filter κ)) :
    (zeroAtFilterExtend A M j f : ι → M) = Function.extend j (f : κ → M) 0 := (rfl)

/-- Extension by zero composes along injective maps. -/
theorem zeroAtFilterExtend_comp {κ ι γ : Type*} {j₁ : κ → ι} {j₂ : ι → γ}
    (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂) :
    zeroAtFilterExtend A M j₂ ∘ₗ zeroAtFilterExtend A M j₁ = zeroAtFilterExtend A M (j₂ ∘ j₁) :=
  LinearMap.ext fun f ↦ Subtype.ext <| (hj₁.extend_comp hj₂ (f : κ → M) 0).symm

/-- Pulling back along an injective map `j` after extending by zero recovers the original family. -/
theorem zeroAtFilterComap_comp_extend {κ ι : Type*} {j : κ → ι} (hj : Function.Injective j) :
    zeroAtFilterComap A M hj.tendsto_cofinite ∘ₗ zeroAtFilterExtend A M j = LinearMap.id :=
  LinearMap.ext fun f ↦ Subtype.ext <| Function.extend_comp hj (f : κ → M) 0

/-- For any countable index type `ι`, the module of `ι`-indexed null families is an `A`-linear
retract of the module of `ℕ`-indexed null families. -/
theorem exists_retract_zeroAtFilterSubmodule_nat (ι : Type*) [Countable ι] :
    ∃ (emb : zeroAtFilterSubmodule (β := M) A (cofinite : Filter ι) →ₗ[A]
          zeroAtFilterSubmodule (β := M) A (cofinite : Filter ℕ))
      (proj : zeroAtFilterSubmodule (β := M) A (cofinite : Filter ℕ) →ₗ[A]
          zeroAtFilterSubmodule (β := M) A (cofinite : Filter ι)),
      proj ∘ₗ emb = LinearMap.id :=
  let ⟨j, hj⟩ := Countable.exists_injective_nat ι
  ⟨zeroAtFilterExtend A M j, zeroAtFilterComap A M hj.tendsto_cofinite,
    zeroAtFilterComap_comp_extend A M hj⟩

end SubmoduleMaps

end Filter

end
