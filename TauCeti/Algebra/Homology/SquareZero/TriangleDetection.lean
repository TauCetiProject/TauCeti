/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero
import Mathlib.Tactic.Abel

/-!
# The exact triangle detection lemma

Let `(M₀, d₀) → (M₁, d₁) → (M₂, d₂) → ⋯` be a sequence of differential modules and chain maps
`fᵢ : Mᵢ → Mᵢ₊₁` in which each composite `fᵢ₊₁ ∘ fᵢ` is null-homotopic, by a homotopy
`hᵢ : Mᵢ → Mᵢ₊₂` with `fᵢ₊₁ ∘ fᵢ = dᵢ₊₂ ∘ hᵢ + hᵢ ∘ dᵢ`. The maps

`ψᵢ = fᵢ₊₂ ∘ hᵢ - hᵢ₊₁ ∘ fᵢ : Mᵢ → Mᵢ₊₃`

then satisfy `dᵢ₊₃ ∘ ψᵢ = -ψᵢ ∘ dᵢ`, so they send cycles to cycles and boundaries to boundaries.
The **exact triangle detection lemma** of Ozsváth and Szabó says that if the `ψᵢ` induce
isomorphisms on homology, then the homology of the cone of `fᵢ` is the homology of `Mᵢ₊₂`, and
the sequence of homologies is exact. When the sequence is periodic of period three, `Mᵢ₊₃ = Mᵢ`,
this is an exact triangle

`H(M₀) → H(M₁) → H(M₂) → H(M₀)`.

This is how the surgery exact triangles of Heegaard Floer homology are proved: the maps `fᵢ`
count holomorphic triangles, the homotopies `hᵢ` count holomorphic quadrilaterals, and the `ψᵢ`
are shown to be quasi-isomorphisms by an area filtration argument.

Only a few of the hypotheses are needed for each conclusion, and they are stated elementwise, in
the form of `LinearMap.homologyMap_surjective_iff` and `LinearMap.homologyMap_injective_iff`:
`ψᵢ` is surjective on homology when every cycle of `dᵢ₊₃` differs from the image of a cycle of
`dᵢ` by a boundary, and injective on homology when a cycle of `dᵢ` whose image is a boundary is
a boundary. Since `ψᵢ` anticommutes with the differentials rather than commuting with them, it is
not a chain map in the sense of `LinearMap.homologyMap`, which is why these hypotheses are not
phrased through induced maps.

* **Exactness.** The composite `f₁ ∘ f₀` is zero on homology. If `ψ₀` is surjective and `ψ₁`
  is injective on homology, a cycle `b` of `d₁` with `f₁ b` a boundary is homologous to the image
  of a cycle of `d₀` (`LinearMap.exists_mem_ker_sub_mem_range_of_triangle`). Indeed, if
  `f₁ b = d₂ c`, then `h₁ b - f₂ c` is a cycle, homologous to `ψ₀ a` for a cycle `a`, and applying
  `f₃` shows that `ψ₁ (b + f₀ a)` is a boundary. So the induced maps on homology are exact at
  `H(M₁)` (`LinearMap.exact_homologyMap_of_triangle`).
* **The cone.** The map `α (a, b) = h₀ a + f₁ b` from the mapping cone
  `(a, b) ↦ (-d₀ a, f₀ a + d₁ b)` of `f₀` to `M₂` is a chain map
  (`LinearMap.coprod_comp_mappingCone`). If `ψ₀` and `ψ₁` induce isomorphisms on homology and
  `ψ₂` is injective on homology, it induces an isomorphism on homology
  (`LinearMap.homologyMap_coprod_bijective_of_triangle`).
* **Exact triangles.** For three differential modules with chain maps `f₀ : M₀ → M₁`,
  `f₁ : M₁ → M₂`, `f₂ : M₂ → M₀` and homotopies `h₀ : M₀ → M₂`, `h₁ : M₁ → M₀`,
  `h₂ : M₂ → M₁`, if the three maps `ψᵢ : Mᵢ → Mᵢ` induce isomorphisms on homology, the
  homologies form an exact triangle (`LinearMap.exact_homologyMap_of_cyclic_triangle`).

Nothing here needs the coefficients to have characteristic two, and the modules carry no grading.
Over `𝔽₂` the signs disappear, and `ψᵢ = fᵢ₊₂ ∘ hᵢ + hᵢ₊₁ ∘ fᵢ` is the map of Ozsváth and Szabó.

## Main results

* `LinearMap.exists_mem_ker_sub_mem_range_of_triangle`: exactness at `M₁`, elementwise.
* `LinearMap.exact_homologyMap_of_triangle`: the induced maps on homology are exact at `H(M₁)`.
* `LinearMap.homologyMap_coprod_bijective_of_triangle`: the chain map `(a, b) ↦ h₀ a + f₁ b` from
  the cone of `f₀` to `M₂` induces an isomorphism on homology.
* `LinearMap.exact_homologyMap_of_cyclic_triangle`: the exact triangle of homologies.

## References

* P. Ozsváth and Z. Szabó, *On the Heegaard Floer homology of branched double-covers*, Adv. Math.
  **194** (2005), 1--33, [arXiv:math/0309170](https://arxiv.org/abs/math/0309170), Lemma 4.2.
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004), 1159--1245, Section 9 (the surgery exact triangle).
-/

public section

namespace LinearMap

section Sequence

variable {S M₀ M₁ M₂ M₃ M₄ M₅ : Type*} [Ring S]
  [AddCommGroup M₀] [Module S M₀] [AddCommGroup M₁] [Module S M₁]
  [AddCommGroup M₂] [Module S M₂] [AddCommGroup M₃] [Module S M₃]
  [AddCommGroup M₄] [Module S M₄] [AddCommGroup M₅] [Module S M₅]
  {d₀ : M₀ →ₗ[S] M₀} {d₁ : M₁ →ₗ[S] M₁} {d₂ : M₂ →ₗ[S] M₂} {d₃ : M₃ →ₗ[S] M₃}
  {d₄ : M₄ →ₗ[S] M₄} {d₅ : M₅ →ₗ[S] M₅}
  {f₀ : M₀ →ₗ[S] M₁} {f₁ : M₁ →ₗ[S] M₂} {f₂ : M₂ →ₗ[S] M₃} {f₃ : M₃ →ₗ[S] M₄}
  {f₄ : M₄ →ₗ[S] M₅}
  {h₀ : M₀ →ₗ[S] M₂} {h₁ : M₁ →ₗ[S] M₃} {h₂ : M₂ →ₗ[S] M₄} {h₃ : M₃ →ₗ[S] M₅}

/-- **Exactness in the triangle detection lemma**, elementwise. Let `f₀, …, f₃` be chain maps
with null-homotopic composites, `fᵢ₊₁ ∘ fᵢ = dᵢ₊₂ ∘ hᵢ + hᵢ ∘ dᵢ`. Suppose that
`ψ₀ = f₂ ∘ h₀ - h₁ ∘ f₀` is surjective on homology, in the sense that every cycle of `d₃` differs
from `ψ₀` of a cycle of `d₀` by a boundary, and that `ψ₁ = f₃ ∘ h₁ - h₂ ∘ f₁` is injective on
homology, in the sense that a cycle of `d₁` whose image under `ψ₁` is a boundary is a boundary.
Then every cycle `b` of `d₁` such that `f₁ b` is a boundary differs from the image under `f₀` of
a cycle of `d₀` by a boundary. -/
theorem exists_mem_ker_sub_mem_range_of_triangle
    (hf₀ : f₀ ∘ₗ d₀ = d₁ ∘ₗ f₀) (hf₂ : f₂ ∘ₗ d₂ = d₃ ∘ₗ f₂) (hf₃ : f₃ ∘ₗ d₃ = d₄ ∘ₗ f₃)
    (hh₀ : f₁ ∘ₗ f₀ = d₂ ∘ₗ h₀ + h₀ ∘ₗ d₀) (hh₁ : f₂ ∘ₗ f₁ = d₃ ∘ₗ h₁ + h₁ ∘ₗ d₁)
    (hh₂ : f₃ ∘ₗ f₂ = d₄ ∘ₗ h₂ + h₂ ∘ₗ d₂)
    (hψ₀ : ∀ n ∈ ker d₃, ∃ m ∈ ker d₀, n - (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃)
    (hψ₁' : ∀ m ∈ ker d₁, (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄ → m ∈ range d₁)
    {b : M₁} (hb : b ∈ ker d₁) (hfb : f₁ b ∈ range d₂) :
    ∃ a ∈ ker d₀, b - f₀ a ∈ range d₁ := by
  simp only [LinearMap.ext_iff, comp_apply, LinearMap.add_apply] at hf₀ hf₂ hf₃ hh₀ hh₁ hh₂
  rw [mem_ker] at hb
  obtain ⟨c, hc⟩ := hfb
  -- `h₁ b - f₂ c` is a cycle, homologous to `ψ₀ a` for a cycle `a`.
  obtain ⟨a, ha, e, he⟩ := hψ₀ (h₁ b - f₂ c) (by simp [← hf₂, hc, hh₁, hb])
  rw [mem_ker] at ha
  have hd₂h₀ : d₂ (h₀ a) = f₁ (f₀ a) := by simp [hh₀, ha]
  -- Applying `f₃` shows that `ψ₁ (b + f₀ a)` is a boundary.
  have hb' : b + f₀ a ∈ range d₁ := by
    refine hψ₁' _ (by simp [hb, ← hf₀, ha]) ⟨f₃ e + h₂ c + h₂ (h₀ a), ?_⟩
    have he' := congr(f₃ $he)
    simp only [hf₃, map_sub, LinearMap.sub_apply, comp_apply, hh₂, hc, hd₂h₀] at he'
    simp only [map_add, he', LinearMap.sub_apply, comp_apply]
    abel
  exact ⟨-a, by simpa using ha, by simpa [sub_eq_add_neg] using hb'⟩

/-- **Exactness in the triangle detection lemma.** Let `f₀, …, f₃` be chain maps with
null-homotopic composites, `fᵢ₊₁ ∘ fᵢ = dᵢ₊₂ ∘ hᵢ + hᵢ ∘ dᵢ`. If `ψ₀ = f₂ ∘ h₀ - h₁ ∘ f₀` is
surjective on homology and `ψ₁ = f₃ ∘ h₁ - h₂ ∘ f₁` is injective on homology, both stated
elementwise, then the maps induced by `f₀` and `f₁` on homology are exact at `H(M₁)`. -/
theorem exact_homologyMap_of_triangle (hd₀ : d₀ ∘ₗ d₀ = 0) (hd₁ : d₁ ∘ₗ d₁ = 0)
    (hd₂ : d₂ ∘ₗ d₂ = 0) (hf₀ : f₀ ∘ₗ d₀ = d₁ ∘ₗ f₀) (hf₁ : f₁ ∘ₗ d₁ = d₂ ∘ₗ f₁)
    (hf₂ : f₂ ∘ₗ d₂ = d₃ ∘ₗ f₂) (hf₃ : f₃ ∘ₗ d₃ = d₄ ∘ₗ f₃)
    (hh₀ : f₁ ∘ₗ f₀ = d₂ ∘ₗ h₀ + h₀ ∘ₗ d₀) (hh₁ : f₂ ∘ₗ f₁ = d₃ ∘ₗ h₁ + h₁ ∘ₗ d₁)
    (hh₂ : f₃ ∘ₗ f₂ = d₄ ∘ₗ h₂ + h₂ ∘ₗ d₂)
    (hψ₀ : ∀ n ∈ ker d₃, ∃ m ∈ ker d₀, n - (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃)
    (hψ₁' : ∀ m ∈ ker d₁, (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄ → m ∈ range d₁) :
    Function.Exact (homologyMap f₀ hd₀ hd₁ hf₀) (homologyMap f₁ hd₁ hd₂ hf₁) := by
  intro y
  constructor
  · intro hy
    obtain ⟨b, rfl⟩ := d₁.homologyπ_surjective hd₁ y
    rw [homologyπ_apply, homologyMap_mk, Submodule.Quotient.mk_eq_zero, mem_boundariesInKer] at hy
    obtain ⟨a, ha, hab⟩ := exists_mem_ker_sub_mem_range_of_triangle hf₀ hf₂ hf₃ hh₀ hh₁ hh₂ hψ₀
      hψ₁' b.property hy
    refine ⟨d₀.homologyπ hd₀ ⟨a, ha⟩, ?_⟩
    simpa [homologyπ_apply, Submodule.Quotient.eq, mem_boundariesInKer] using neg_mem hab
  · rintro ⟨x, rfl⟩
    rw [homologyMap_homologyMap,
      homologyMap_eq_of_sub_eq (f₁ ∘ₗ f₀) 0 h₀ hd₀ hd₂ _ (by simp) (by simpa using hh₀),
      homologyMap_zero, LinearMap.zero_apply]

/-- The injectivity half of `LinearMap.homologyMap_coprod_bijective_of_triangle`: a cycle of
the mapping cone of `f₀` whose image `h₀ a + f₁ b` is a boundary is a boundary. -/
private theorem mem_range_mappingCone_of_triangle
    (hf₀ : f₀ ∘ₗ d₀ = d₁ ∘ₗ f₀) (hf₂ : f₂ ∘ₗ d₂ = d₃ ∘ₗ f₂) (hf₃ : f₃ ∘ₗ d₃ = d₄ ∘ₗ f₃)
    (hh₀ : f₁ ∘ₗ f₀ = d₂ ∘ₗ h₀ + h₀ ∘ₗ d₀) (hh₁ : f₂ ∘ₗ f₁ = d₃ ∘ₗ h₁ + h₁ ∘ₗ d₁)
    (hh₂ : f₃ ∘ₗ f₂ = d₄ ∘ₗ h₂ + h₂ ∘ₗ d₂)
    (hψ₀ : ∀ n ∈ ker d₃, ∃ m ∈ ker d₀, n - (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃)
    (hψ₀' : ∀ m ∈ ker d₀, (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃ → m ∈ range d₀)
    (hψ₁' : ∀ m ∈ ker d₁, (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄ → m ∈ range d₁)
    (x : M₀ × M₁) (hx : x ∈ ker (mappingCone d₀ d₁ f₀)) (hαx : h₀.coprod f₁ x ∈ range d₂) :
    x ∈ range (mappingCone d₀ d₁ f₀) := by
  have key {b : M₁} :=
    exists_mem_ker_sub_mem_range_of_triangle (b := b) hf₀ hf₂ hf₃ hh₀ hh₁ hh₂ hψ₀ hψ₁'
  simp only [LinearMap.ext_iff, comp_apply, LinearMap.add_apply] at hf₀ hf₂ hh₀ hh₁
  obtain ⟨a, b⟩ := x
  obtain ⟨c, hc⟩ := hαx
  simp only [mem_ker, mappingCone_apply, Prod.mk_eq_zero, neg_eq_zero] at hx
  obtain ⟨ha, hab⟩ := hx
  simp only [coprod_apply] at hc
  -- `ψ₀ a` is the boundary of `f₂ c - h₁ b`, so `a = d₀ x`.
  obtain ⟨x, rfl⟩ := hψ₀' a (mem_ker.mpr ha) ⟨f₂ c - h₁ b, by
    have hb : d₁ b = -f₀ a := eq_neg_of_add_eq_zero_right hab
    simp only [map_sub, ← hf₂, hc, map_add, hh₁, hb, map_neg, LinearMap.sub_apply, comp_apply]
    abel⟩
  -- Then `b + f₀ x` is a cycle whose image under `f₁` is a boundary, so it comes from `M₀`.
  have hbx : b + f₀ x ∈ ker d₁ := by
    rw [mem_ker, map_add, ← hf₀]
    exact (add_comm _ _).trans hab
  obtain ⟨a', ha', y, hy⟩ := key hbx ⟨c + h₀ x, by
    simp only [map_add, hc, hh₀]
    abel⟩
  refine ⟨(a' - x, y), ?_⟩
  simp only [mappingCone_apply, map_sub, mem_ker.mp ha', zero_sub, neg_neg, Prod.mk.injEq,
    true_and, hy]
  abel

/-- The surjectivity half of `LinearMap.homologyMap_coprod_bijective_of_triangle`: every cycle of
`d₂` differs from the image `h₀ a + f₁ b` of a cycle of the mapping cone of `f₀` by a
boundary. -/
private theorem exists_mem_ker_mappingCone_sub_mem_range_of_triangle
    (hf₀ : f₀ ∘ₗ d₀ = d₁ ∘ₗ f₀) (hf₁ : f₁ ∘ₗ d₁ = d₂ ∘ₗ f₁)
    (hf₂ : f₂ ∘ₗ d₂ = d₃ ∘ₗ f₂) (hf₃ : f₃ ∘ₗ d₃ = d₄ ∘ₗ f₃) (hf₄ : f₄ ∘ₗ d₄ = d₅ ∘ₗ f₄)
    (hh₀ : f₁ ∘ₗ f₀ = d₂ ∘ₗ h₀ + h₀ ∘ₗ d₀) (hh₁ : f₂ ∘ₗ f₁ = d₃ ∘ₗ h₁ + h₁ ∘ₗ d₁)
    (hh₂ : f₃ ∘ₗ f₂ = d₄ ∘ₗ h₂ + h₂ ∘ₗ d₂) (hh₃ : f₄ ∘ₗ f₃ = d₅ ∘ₗ h₃ + h₃ ∘ₗ d₃)
    (hψ₀ : ∀ n ∈ ker d₃, ∃ m ∈ ker d₀, n - (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃)
    (hψ₁ : ∀ n ∈ ker d₄, ∃ m ∈ ker d₁, n - (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄)
    (hψ₁' : ∀ m ∈ ker d₁, (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄ → m ∈ range d₁)
    (hψ₂' : ∀ m ∈ ker d₂, (f₄ ∘ₗ h₂ - h₃ ∘ₗ f₂) m ∈ range d₅ → m ∈ range d₂)
    (c : M₂) (hc : c ∈ ker d₂) :
    ∃ x ∈ ker (mappingCone d₀ d₁ f₀), c - h₀.coprod f₁ x ∈ range d₂ := by
  have key {c : M₂} :=
    exists_mem_ker_sub_mem_range_of_triangle (b := c) hf₁ hf₃ hf₄ hh₁ hh₂ hh₃ hψ₁ hψ₂'
  simp only [LinearMap.ext_iff, comp_apply, LinearMap.add_apply] at hf₀ hf₁ hf₂ hf₃ hh₀ hh₁ hh₂
  rw [mem_ker] at hc
  obtain ⟨a, ha, e, he⟩ := hψ₀ (f₂ c) (by simp [← hf₂, hc])
  rw [mem_ker] at ha
  simp only [LinearMap.sub_apply, comp_apply] at he
  have hd₂h₀ : d₂ (h₀ a) = f₁ (f₀ a) := by simp [hh₀, ha]
  -- `ψ₁ (f₀ a)` is a boundary, so `f₀ a = d₁ b` for some `b`.
  obtain ⟨b, hb⟩ := hψ₁' (f₀ a) (by simp [← hf₀, ha])
    ⟨h₂ (h₀ a) - h₂ c + f₃ e, by
      simp only [map_add, map_sub, ← hf₃, he, LinearMap.sub_apply, comp_apply, hh₂, hc, hd₂h₀,
        map_zero, add_zero]
      abel⟩
  -- `c - h₀ a + f₁ b` is a cycle killed by `f₂` in homology, so it comes from `M₁`.
  have hc' : c - (h₀ a + f₁ (-b)) ∈ ker d₂ := by
    simp only [mem_ker, map_sub, map_add, map_neg, hd₂h₀, ← hf₁, hb, hc]
    abel
  obtain ⟨b', hb', z, hz⟩ := key hc' ⟨e - h₁ (-b), by
    simp only [map_sub, map_add, map_neg, he, hh₁, hb]
    abel⟩
  refine ⟨(a, -b + b'), by simp [ha, hb, mem_ker.mp hb'], z, ?_⟩
  rw [hz, coprod_apply, map_add]
  abel

/-- **The triangle detection lemma.** Let `f₀, …, f₄` be chain maps with null-homotopic
composites, `fᵢ₊₁ ∘ fᵢ = dᵢ₊₂ ∘ hᵢ + hᵢ ∘ dᵢ`, and suppose that the maps
`ψᵢ = fᵢ₊₂ ∘ hᵢ - hᵢ₊₁ ∘ fᵢ` induce isomorphisms on homology for `i = 0, 1` and an injection
for `i = 2`, all stated elementwise. Then the chain map `(a, b) ↦ h₀ a + f₁ b` from the mapping
cone of `f₀` to `M₂` induces an isomorphism on homology. -/
theorem homologyMap_coprod_bijective_of_triangle (hd₀ : d₀ ∘ₗ d₀ = 0) (hd₁ : d₁ ∘ₗ d₁ = 0)
    (hd₂ : d₂ ∘ₗ d₂ = 0) (hf₀ : f₀ ∘ₗ d₀ = d₁ ∘ₗ f₀) (hf₁ : f₁ ∘ₗ d₁ = d₂ ∘ₗ f₁)
    (hf₂ : f₂ ∘ₗ d₂ = d₃ ∘ₗ f₂) (hf₃ : f₃ ∘ₗ d₃ = d₄ ∘ₗ f₃) (hf₄ : f₄ ∘ₗ d₄ = d₅ ∘ₗ f₄)
    (hh₀ : f₁ ∘ₗ f₀ = d₂ ∘ₗ h₀ + h₀ ∘ₗ d₀) (hh₁ : f₂ ∘ₗ f₁ = d₃ ∘ₗ h₁ + h₁ ∘ₗ d₁)
    (hh₂ : f₃ ∘ₗ f₂ = d₄ ∘ₗ h₂ + h₂ ∘ₗ d₂) (hh₃ : f₄ ∘ₗ f₃ = d₅ ∘ₗ h₃ + h₃ ∘ₗ d₃)
    (hψ₀ : ∀ n ∈ ker d₃, ∃ m ∈ ker d₀, n - (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃)
    (hψ₀' : ∀ m ∈ ker d₀, (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₃ → m ∈ range d₀)
    (hψ₁ : ∀ n ∈ ker d₄, ∃ m ∈ ker d₁, n - (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄)
    (hψ₁' : ∀ m ∈ ker d₁, (f₃ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₄ → m ∈ range d₁)
    (hψ₂' : ∀ m ∈ ker d₂, (f₄ ∘ₗ h₂ - h₃ ∘ₗ f₂) m ∈ range d₅ → m ∈ range d₂) :
    Function.Bijective (homologyMap (h₀.coprod f₁) (mappingCone_comp_self f₀ hd₀ hd₁ hf₀) hd₂
      (coprod_comp_mappingCone hf₁ hh₀)) := by
  rw [Function.Bijective, homologyMap_injective_iff, homologyMap_surjective_iff]
  exact ⟨mem_range_mappingCone_of_triangle hf₀ hf₂ hf₃ hh₀ hh₁ hh₂ hψ₀ hψ₀' hψ₁',
    exists_mem_ker_mappingCone_sub_mem_range_of_triangle hf₀ hf₁ hf₂ hf₃ hf₄ hh₀ hh₁ hh₂ hh₃ hψ₀
      hψ₁ hψ₁' hψ₂'⟩

end Sequence

section Cyclic

variable {S M₀ M₁ M₂ : Type*} [Ring S]
  [AddCommGroup M₀] [Module S M₀] [AddCommGroup M₁] [Module S M₁]
  [AddCommGroup M₂] [Module S M₂]
  {d₀ : M₀ →ₗ[S] M₀} {d₁ : M₁ →ₗ[S] M₁} {d₂ : M₂ →ₗ[S] M₂}
  {f₀ : M₀ →ₗ[S] M₁} {f₁ : M₁ →ₗ[S] M₂} {f₂ : M₂ →ₗ[S] M₀}
  {h₀ : M₀ →ₗ[S] M₂} {h₁ : M₁ →ₗ[S] M₀} {h₂ : M₂ →ₗ[S] M₁}

/-- **The exact triangle detection lemma.** Let `f₀ : M₀ → M₁`, `f₁ : M₁ → M₂` and
`f₂ : M₂ → M₀` be chain maps whose consecutive composites are null-homotopic,
`f₁ ∘ f₀ = d₂ ∘ h₀ + h₀ ∘ d₀`, `f₂ ∘ f₁ = d₀ ∘ h₁ + h₁ ∘ d₁` and
`f₀ ∘ f₂ = d₁ ∘ h₂ + h₂ ∘ d₂`. If the three maps `ψ₀ = f₂ ∘ h₀ - h₁ ∘ f₀`,
`ψ₁ = f₀ ∘ h₁ - h₂ ∘ f₁` and `ψ₂ = f₁ ∘ h₂ - h₀ ∘ f₂` induce isomorphisms on homology, stated
elementwise, then the induced maps on homology form an exact triangle
`H(M₀) → H(M₁) → H(M₂) → H(M₀)`. -/
theorem exact_homologyMap_of_cyclic_triangle (hd₀ : d₀ ∘ₗ d₀ = 0) (hd₁ : d₁ ∘ₗ d₁ = 0)
    (hd₂ : d₂ ∘ₗ d₂ = 0) (hf₀ : f₀ ∘ₗ d₀ = d₁ ∘ₗ f₀) (hf₁ : f₁ ∘ₗ d₁ = d₂ ∘ₗ f₁)
    (hf₂ : f₂ ∘ₗ d₂ = d₀ ∘ₗ f₂)
    (hh₀ : f₁ ∘ₗ f₀ = d₂ ∘ₗ h₀ + h₀ ∘ₗ d₀) (hh₁ : f₂ ∘ₗ f₁ = d₀ ∘ₗ h₁ + h₁ ∘ₗ d₁)
    (hh₂ : f₀ ∘ₗ f₂ = d₁ ∘ₗ h₂ + h₂ ∘ₗ d₂)
    (hψ₀ : ∀ n ∈ ker d₀, ∃ m ∈ ker d₀, n - (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₀)
    (hψ₀' : ∀ m ∈ ker d₀, (f₂ ∘ₗ h₀ - h₁ ∘ₗ f₀) m ∈ range d₀ → m ∈ range d₀)
    (hψ₁ : ∀ n ∈ ker d₁, ∃ m ∈ ker d₁, n - (f₀ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₁)
    (hψ₁' : ∀ m ∈ ker d₁, (f₀ ∘ₗ h₁ - h₂ ∘ₗ f₁) m ∈ range d₁ → m ∈ range d₁)
    (hψ₂ : ∀ n ∈ ker d₂, ∃ m ∈ ker d₂, n - (f₁ ∘ₗ h₂ - h₀ ∘ₗ f₂) m ∈ range d₂)
    (hψ₂' : ∀ m ∈ ker d₂, (f₁ ∘ₗ h₂ - h₀ ∘ₗ f₂) m ∈ range d₂ → m ∈ range d₂) :
    Function.Exact (homologyMap f₀ hd₀ hd₁ hf₀) (homologyMap f₁ hd₁ hd₂ hf₁) ∧
      Function.Exact (homologyMap f₁ hd₁ hd₂ hf₁) (homologyMap f₂ hd₂ hd₀ hf₂) ∧
      Function.Exact (homologyMap f₂ hd₂ hd₀ hf₂) (homologyMap f₀ hd₀ hd₁ hf₀) :=
  ⟨exact_homologyMap_of_triangle hd₀ hd₁ hd₂ hf₀ hf₁ hf₂ hf₀ hh₀ hh₁ hh₂ hψ₀ hψ₁',
    exact_homologyMap_of_triangle hd₁ hd₂ hd₀ hf₁ hf₂ hf₀ hf₁ hh₁ hh₂ hh₀ hψ₁ hψ₂',
    exact_homologyMap_of_triangle hd₂ hd₀ hd₁ hf₂ hf₀ hf₁ hf₂ hh₂ hh₀ hh₁ hψ₂ hψ₀'⟩

end Cyclic

end LinearMap
