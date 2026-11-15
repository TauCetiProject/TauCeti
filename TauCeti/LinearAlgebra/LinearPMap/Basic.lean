/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Basic lemmas on partial linear maps

General lemmas on `LinearPMap` that Mathlib does not provide.

## Main results

* `LinearPMap.congr_fun`: the value-level part of `LinearPMap.ext_iff`, with the two domain
  memberships as explicit arguments.
* `LinearPMap.neg_smul` and `LinearPMap.smul_neg`: a negation moves through a scalar multiple.
* `LinearPMap.exists_eq_add_smul_supSpanSingleton`: every vector of the domain of
  `f.supSpanSingleton x y hx` is `s + c • x` with `s` in the domain of `f`, sent to `f s + σ c • y`.
* `LinearPMap.supSpanSingleton_injective`: extending an injective partial map by `x ↦ y` with `y`
  outside its range keeps it injective.
-/

public section

namespace LinearPMap

variable {R S E F : Type*} [Ring R] [Ring S] {σ : R →+* S} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module S F]

/-- Equal partial linear maps take equal values: the value-level part of `LinearPMap.ext_iff`,
with the two domain memberships as explicit arguments. -/
protected theorem congr_fun {f g : E →ₛₗ.[σ] F} (h : f = g) {x : E} (hf : x ∈ f.domain)
    (hg : x ∈ g.domain) : f ⟨x, hf⟩ = g ⟨x, hg⟩ :=
  (LinearPMap.ext_iff.mp h).2 (x := x) (hf := hf) (hg := hg)

/-- Negating the scalar negates the scalar multiple of a partial linear map (`LinearPMap` is not a
module, so this is not an instance of `neg_smul`). -/
@[simp]
theorem neg_smul {M : Type*} [Ring M] [Module M F] [SMulCommClass S M F] (c : M)
    (A : E →ₛₗ.[σ] F) : (-c) • A = -(c • A) :=
  LinearPMap.ext rfl fun _ _ _ => _root_.neg_smul _ _

/-- Negating the map negates the scalar multiple of a partial linear map. -/
@[simp]
theorem smul_neg {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass S M F] (c : M)
    (A : E →ₛₗ.[σ] F) : c • (-A) = -(c • A) :=
  LinearPMap.ext rfl fun _ _ _ => _root_.smul_neg _ _

section supSpanSingleton

variable {K L : Type*} [DivisionRing K] [DivisionRing L] {σ : K →+* L} [Module K E] [Module L F]

/-- Every vector of the domain of `f.supSpanSingleton x y hx` is `s + c • x` with `s` in the domain
of `f`, and the extension sends it to `f s + σ c • y`. -/
theorem exists_eq_add_smul_supSpanSingleton (f : E →ₛₗ.[σ] F) {x : E} (y : F)
    (hx : x ∉ f.domain) (z : (f.supSpanSingleton x y hx).domain) :
    ∃ (s : f.domain) (c : K),
      (z : E) = s + c • x ∧ f.supSpanSingleton x y hx z = f s + σ c • y := by
  obtain ⟨z, hz⟩ := z
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨⟨s, hs⟩, c, rfl, supSpanSingleton_apply_mk f x y hx s hs c⟩

/-- Extending an injective partial map by `x ↦ y` with `y` outside its range keeps it injective. -/
theorem supSpanSingleton_injective {f : E →ₛₗ.[σ] F} (hf : Function.Injective f) {x : E} {y : F}
    (hx : x ∉ f.domain) (hy : y ∉ Set.range f) :
    Function.Injective (f.supSpanSingleton x y hx) := by
  rw [← coe_toFun_eq_coe]
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨s, c, hz', hfz⟩ := exists_eq_add_smul_supSpanSingleton f y hx z
  rw [toFun_eq_coe, hfz] at hz
  obtain rfl : c = 0 := by
    by_contra hc
    refine hy ⟨-c⁻¹ • s, ?_⟩
    rw [map_smulₛₗ, eq_neg_of_add_eq_zero_left hz]
    simp [smul_smul, ← _root_.map_mul, hc]
  rw [_root_.map_zero, zero_smul, add_zero, ← f.map_zero] at hz
  ext
  simp [hz', hf hz]

end supSpanSingleton

end LinearPMap

end
