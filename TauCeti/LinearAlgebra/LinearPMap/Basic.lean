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
* `LinearPMap.eq_of_le_of_smul_sub_surjective_of_injective`: an extension `B` of `A` equals `A`
  when `lambda • I - A` is surjective and `lambda • I - B` is injective.
* `LinearPMap.exists_eq_add_smul_supSpanSingleton`: every vector of the domain of
  `f.supSpanSingleton x y hx` is `s + c • x` with `s` in the domain of `f`, sent to `f s + σ c • y`.
* `LinearPMap.supSpanSingleton_injective`: extending an injective partial map by `x ↦ y` with `y`
  outside its range keeps it injective.
* `LinearPMap.mem_ker_iff_mem_graph`: the kernel consists of the vectors `x` with `(x, 0)` in the
  graph.
* `LinearPMap.compLinearMap`: maximal-domain composition `g ∘ f` of a partial linear map `g` with
  an everywhere-defined linear map `f`, on `g.domain.comap f`, together with domain, evaluation, and
  simplification lemmas (`LinearMap.compPMap_domain`, `LinearPMap.comp_domain`,
  `LinearPMap.comp_apply`, `LinearPMap.compLinearMap_domain`, `LinearPMap.mem_compLinearMap_domain`,
  `LinearPMap.compLinearMap_apply`, `LinearPMap.compLinearMap_id`, `LinearPMap.zero_compLinearMap`,
  `LinearPMap.compLinearMap_zero`, and `LinearMap.toPMap_compLinearMap`).
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

/-- **An operator has no proper extension on which a shift stays injective.** If `A ≤ B`,
`lambda • I - A` maps `D(A)` onto `E` and `lambda • I - B` is injective on `D(B)`, then `A = B`.

Unlike `LinearPMap.eq_of_le_of_mem_resolventSet`, no continuity or bounded inverse is required,
so it applies when injectivity of `lambda • I - B` is all that is known about the extension. -/
theorem eq_of_le_of_smul_sub_surjective_of_injective {A B : E →ₗ.[R] E} {lambda : R}
    (hAB : A ≤ B) (hA : Function.Surjective fun x : A.domain => lambda • (x : E) - A x)
    (hB : Function.Injective fun x : B.domain => lambda • (x : E) - B x) : A = B := by
  -- A vector `y ∈ D(B)` has `lambda • y - B y = lambda • x - A x` for some `x ∈ D(A)`;
  -- injectivity for `B` then forces `y = x`, so `D(B) ⊆ D(A)`.
  refine eq_of_le_of_domain_eq hAB (le_antisymm hAB.1 fun y hy => ?_)
  obtain ⟨x, hx⟩ := hA (lambda • y - B ⟨y, hy⟩)
  obtain ⟨x', hx'coe, hx'val⟩ := exists_of_le hAB x
  have hxy : x' = (⟨y, hy⟩ : B.domain) := by
    refine hB ?_
    simp only [← hx'coe, ← hx'val]
    exact hx
  have hcoe : (x : E) = y := by rw [hx'coe, hxy]
  rw [← hcoe]
  exact x.property

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

/-- A vector lies in the kernel of a partial linear map exactly when `(x, 0)` lies in its graph. -/
theorem mem_ker_iff_mem_graph {M : Type*} [AddCommGroup M] [Module R M] (f : E →ₗ.[R] M) {x : E} :
    x ∈ f.ker ↔ (x, 0) ∈ f.graph := by
  simp [mem_ker_iff, eq_comm]

section Comp

variable {T G : Type*} [Ring T] {τ : S →+* T} {ρ : R →+* T} [RingHomCompTriple σ τ ρ]
  [AddCommGroup G] [Module T G]

/-- Composing a linear map on the left with a partial linear map preserves the domain. -/
@[simp]
theorem _root_.LinearMap.compPMap_domain (g : F →ₛₗ[τ] G) (f : E →ₛₗ.[σ] F) :
    (g.compPMap (ρ := ρ) f).domain = f.domain :=
  (rfl)

/-- Composing two partial linear maps gives a partial linear map on the inner map's domain. -/
@[simp]
theorem comp_domain (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F) (H : ∀ x : f.domain, f x ∈ g.domain) :
    (g.comp (ρ := ρ) f H).domain = f.domain :=
  (rfl)

/-- Evaluating a composition `g.comp f H` applies `g` to `f x`. -/
@[simp]
theorem comp_apply (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F) (H : ∀ x : f.domain, f x ∈ g.domain)
    (x : (g.comp (ρ := ρ) f H).domain) :
    g.comp (ρ := ρ) f H x = g ⟨f ⟨x, x.property⟩, H ⟨x, x.property⟩⟩ :=
  (rfl)

/-- Compose a partial linear map `g` on the right with an everywhere-defined linear map `f` on its
maximal domain `g.domain.comap f`. -/
def compLinearMap (g : F →ₛₗ.[τ] G) (f : E →ₛₗ[σ] F) : E →ₛₗ.[ρ] G :=
  g.comp (ρ := ρ) (f.toPMap (g.domain.comap f)) fun x ↦ x.property

/-- Unfolding lemma: `g.compLinearMap f` is `g.comp` with `f.toPMap (g.domain.comap f)`. -/
theorem compLinearMap_def (g : F →ₛₗ.[τ] G) (f : E →ₛₗ[σ] F) :
    g.compLinearMap (ρ := ρ) f =
      g.comp (ρ := ρ) (f.toPMap (g.domain.comap f)) fun x ↦ x.property :=
  (rfl)

/-- The domain of `g.compLinearMap f` is the preimage `g.domain.comap f`. -/
@[simp]
theorem compLinearMap_domain (g : F →ₛₗ.[τ] G) (f : E →ₛₗ[σ] F) :
    (g.compLinearMap (ρ := ρ) f).domain = g.domain.comap f :=
  (rfl)

/-- A vector belongs to the domain of `g.compLinearMap f` if and only if `f x ∈ g.domain`. -/
theorem mem_compLinearMap_domain (g : F →ₛₗ.[τ] G) (f : E →ₛₗ[σ] F) {x : E} :
    x ∈ (g.compLinearMap (ρ := ρ) f).domain ↔ f x ∈ g.domain := by
  rw [compLinearMap_domain, Submodule.mem_comap]

/-- Evaluating `g.compLinearMap f` at `x` applies `g` to `f x`. -/
@[simp]
theorem compLinearMap_apply (g : F →ₛₗ.[τ] G) (f : E →ₛₗ[σ] F)
    (x : (g.compLinearMap (ρ := ρ) f).domain) :
    g.compLinearMap (ρ := ρ) f x =
      g ⟨f x, (mem_compLinearMap_domain (ρ := ρ) g f).mp x.property⟩ :=
  (rfl)

/-- Right-composing a partial linear map with the identity linear map does nothing. -/
@[simp]
theorem compLinearMap_id (g : E →ₛₗ.[σ] F) :
    g.compLinearMap (LinearMap.id : E →ₗ[R] E) = g :=
  LinearPMap.ext (Submodule.comap_id g.domain) fun x _ _ ↦ by
    rw [compLinearMap_apply]
    exact congrArg g (Subtype.ext (LinearMap.id_apply x))

/-- Left-composing the zero partial linear map with a linear map gives zero. -/
@[simp]
theorem zero_compLinearMap (f : E →ₛₗ[σ] F) :
    (0 : F →ₛₗ.[τ] G).compLinearMap (ρ := ρ) f = 0 :=
  LinearPMap.ext (Submodule.comap_top f) fun _ _ _ ↦ by
    rw [compLinearMap_apply, zero_apply, zero_apply]

/-- Right-composing a partial linear map with the zero linear map gives zero. -/
@[simp]
theorem compLinearMap_zero (g : F →ₛₗ.[τ] G) :
    g.compLinearMap (ρ := ρ) (0 : E →ₛₗ[σ] F) = 0 :=
  LinearPMap.ext (by ext; simp) fun x _ _ ↦ by
    rw [compLinearMap_apply, zero_apply]
    exact (congrArg g (Subtype.ext (LinearMap.zero_apply x))).trans g.map_zero

/-- Restricting `g` to `p` and right-composing with `f` restricts `g ∘ f` to `p.comap f`. -/
@[simp]
theorem _root_.LinearMap.toPMap_compLinearMap (g : F →ₛₗ[τ] G) (p : Submodule S F)
    (f : E →ₛₗ[σ] F) :
    (g.toPMap p).compLinearMap (ρ := ρ) f = (g.comp f).toPMap (p.comap f) :=
  LinearPMap.ext (by simp) fun _ _ _ ↦ by
    simp [compLinearMap_apply]

end Comp

end LinearPMap

end
