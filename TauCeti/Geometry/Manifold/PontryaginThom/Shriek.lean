/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.AbsoluteRelative
public import TauCeti.Geometry.Manifold.PontryaginThom.FundamentalClass
import TauCeti.AlgebraicTopology.Cohomology.Cap.CrossRel

/-!
# The shriek map of a framed submanifold and Poincaré duality

Let `τ : S × V → M` be a framed tube around `f : S → M` (`TauCeti.IsFramedTube`) with closed core
`f(S)`, with `V` a real normed space of dimension `r ≠ 0`, and let `o` generate the local homology
`H_r(V, V ∖ 0; k)`. The **shriek map** `i_!` of the framed submanifold sends a class `y` of `M` to
the class `x` of `S` such that the image of `y` in `H(M, M ∖ f(S))` is `τ_*(o × x)`: it is the map
to the homology relative to the complement of the core, followed by the inverse of the Thom
isomorphism `x ↦ τ_*(o × x)`
(`TauCeti.IsFramedTube.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap`).
This file computes it on cap products:

`i_!(z ⌢ φ) = (-1)^(r j) i_!(z) ⌢ f^* φ`

for `z ∈ H(M; k ⊗ L)` and `φ ∈ Hʲ(M; k)`
(`TauCeti.IsFramedTube.singularHomologyπ_singularCap_eq`). For a fundamental class `[M]`, the class
`[S] = i_![M]` is a fundamental class of `S`
(`TauCeti.IsFramedTube.isFundamentalClass_of_singularHomologyπ_eq`), so `i_!` sends the
Poincaré dual `[M] ⌢ φ` of `φ` to `(-1)^(r j)` times the Poincaré dual `[S] ⌢ f^* φ` of its
restriction
(`TauCeti.IsFramedTube.exists_isFundamentalClass_forall_singularHomologyπ_singularCap_eq`).
Informally, when `L` is the tensor unit and capping with `[M]` is bijective, as it is for the
fundamental class of a closed oriented manifold with integral coefficients
(`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`, stated for that class and
its own cap product convention), this determines the shriek map as
`i_! = (-1)^(r j) D_S ∘ f^* ∘ D_M⁻¹`, with `D` the cap product with the fundamental class. That
composite is not formalized here.

The codimension-zero case `r = 0` is excluded: the computation below inverts the Thom isomorphism
by the homology Thom map of `TopCat.singularCap_singularHomologyCrossRel_of_isZero`, which is only
available in positive degree.

The sign comes from the orientation convention: here `[M]` restricts along the core to `o × [S]`,
*the fibre followed by the core*. Barraud–Damian–Humilière–Oancea orient the core first
(Remark 9.2.4) and state the formula `i_! = D_S ∘ f^* ∘ D_M⁻¹` without a sign in that convention
(Proposition 11.3.2); the exchange of factors relating the two conventions is not used here.

The computation happens in the Thom pair `(V × S, (V ∖ 0) × S)` of the product bundle, to which
excision along the tube reduces it: there

`(o × x) ⌢ pr₂^* ψ = (-1)^(r j) o × (x ⌢ ψ)`

for `ψ ∈ Hʲ(S; k)` (`TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul`, in
`TauCeti.AlgebraicTopology.Cohomology.Cap.CrossRel`, where it is proved with the homology Thom
map and the projection formula `TopPair.map_singularCap_absoluteSingularCap`).

## Main results

* `TauCeti.IsFramedTube.singularHomologyπ_singularCap_eq`: the shriek map of a framed submanifold
  sends `z ⌢ φ` to `(-1)^(r j) i_!(z) ⌢ f^* φ`.
* `TauCeti.IsFramedTube.exists_isFundamentalClass_forall_singularHomologyπ_singularCap_eq`: the
  shriek map sends the Poincaré dual `[M] ⌢ φ` to `(-1)^(r j) [S] ⌢ f^* φ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remarks 9.2.4 and 9.2.5 and
  Proposition 11.3.2.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products and Poincaré duality) and Section 4.D (the Thom isomorphism).
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Sections 6 and 7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Set
  Topology Module

universe w

namespace TauCeti

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {k : Type w} [CommRing k] (L : ModuleCat.{w} k)

namespace IsFramedTube

variable {S M : Type w} [TopologicalSpace S] [TopologicalSpace M] {f : S → M} {τ : S × V → M}

/-- **The shriek map of a framed submanifold on cap products.** Let `τ : S × V → M` be a framed
tube around `f`, with `V` finite-dimensional, and let `o ∈ H_r(V, V ∖ 0; k)` with `r ≠ 0`. If the
image of `z ∈ H(M; k ⊗ L)` in `H(M, M ∖ f(S))` is the image under the tube of `o × x`, for
`x ∈ H_{j+q}(S; L)`, then for every `φ ∈ Hʲ(M; k)` the image of `z ⌢ φ` is the image under the
tube of `o × ((-1)^(r j) x ⌢ f^* φ)`. When `finrank ℝ V = r`, `f(S)` is closed in a `T₁` space `M`
and `o` generates the local homology, `x` is the image `i_!(z)` of `z` under the shriek map
(`TauCeti.IsFramedTube.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap`), and
this says `i_!(z ⌢ φ) = (-1)^(r j) i_!(z) ⌢ f^* φ`. -/
theorem singularHomologyπ_singularCap_eq (h : IsFramedTube f τ) {r j q n m : ℕ} (hr₀ : r ≠ 0)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r}
    (hn : r + (j + q) = n) (hm : r + q = m) (hjm : j + m = n)
    {x : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj L).obj (TopCat.of S)}
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)}
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r (j + q) n hn (o ⊗ₜ x)))
    (φ : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j) :
    (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) m
        ((TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
          (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z) =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) m
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L r q m hm
          (o ⊗ₜ (((-1 : ℤ) ^ (r * j)) • (TopCat.of S).singularCap k (λ_ L).inv (λ_ L).hom
            j q (j + q) rfl
            (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ) x))) := by
  -- Capping commutes with the map to the relative homology and with the tube.
  have hπ : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) m
        ((TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
          (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z) =
      (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ
        ((TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
          (𝟙_ (ModuleCat.{w} k) ⊗ L) n z) := by
    -- The composite `singularCap ≫ singularHomologyπ` passes through the homology of the ambient
    -- space of the pair, which is `TopCat.of M` only up to unfolding, so `comp_apply` is applied
    -- by unification rather than by `rw`.
    refine (ConcreteCategory.comp_apply _ _ z).symm.trans (Eq.trans ?_
      (ConcreteCategory.comp_apply _ _ z))
    exact (ConcreteCategory.congr_hom (TopPair.singularHomologyπ_comp_absoluteSingularCap
      (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ) k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
      (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ) z).symm
  have hτ := ConcreteCategory.congr_hom (TopPair.absoluteSingularCap_naturality h.tubePairMap k
    (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ)
      (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
        (𝟙_ (ModuleCat.{w} k)) L r (j + q) n hn (o ⊗ₜ x))
  simp only [ConcreteCategory.comp_apply] at hτ
  -- The tube pulls `φ` back to `pr₂^* f^* φ`.
  have hφ : TopCat.singularCohomologyMap (TopPair.Hom.fst h.tubePairMap) j φ =
      TopCat.singularCohomologyMap (snd (TopCat.of V) (TopCat.of S)) j
        (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ) :=
    (ConcreteCategory.congr_hom (h.singularCohomologyMap_tubePairMap _ k _ j) φ).trans
      (ConcreteCategory.comp_apply _ _ φ)
  rw [hπ, hz, ← hτ, hφ, TensorProduct.tmul_smul, map_zsmul]
  -- The source pair of `h.tubePairMap` is the preimage of `{0}ᶜ : Set V`, that of the relative
  -- cross product the preimage of `{0}ᶜ : Set (TopCat.of V)`; they agree only up to unfolding
  -- `TopCat.of`, so the product-pair formula is applied under the push-forward by unification.
  exact congrArg _ (absoluteSingularCap_singularHomologyCrossRel_tmul L (TopCat.of S) hr₀ hn hm hjm
    o (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ) x)

/-- **The shriek map of a framed submanifold through Poincaré duality.** Let `τ : S × V → M` be a
framed tube around `f` with closed core, in a `T₁` space `M`, with `V` of dimension `r ≠ 0`, and let
`o` generate `H_r(V, V ∖ 0; k)`. A fundamental class `[M] ∈ H_{r+q}(M; k ⊗ L)` induces a
fundamental class `[S] ∈ H_q(S; L)`, the image of `[M]` under the shriek map `i_!`, and `i_!` sends
the Poincaré dual `[M] ⌢ φ` of every class `φ ∈ Hʲ(M; k)` to `(-1)^(r j)` times the Poincaré
dual `[S] ⌢ f^* φ` of its restriction to `S`. Informally, when `L` is the tensor unit and capping
with `[M]` is bijective, this determines `i_!` as `(-1)^(r j) D_S ∘ f^* ∘ D_M⁻¹`, with `D` the cap
product with the fundamental class; that composite is not formalized here. The codimension-zero
case `r = 0` is excluded because `TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul` needs
`r ≠ 0`. -/
theorem exists_isFundamentalClass_forall_singularHomologyπ_singularCap_eq [T1Space M]
    (h : IsFramedTube f τ) (hf : IsClosed (range f)) {r q n : ℕ} (hr : finrank ℝ V = r)
    (hr₀ : r ≠ 0)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r} (ho : Submodule.span k {o} = ⊤)
    (hn : r + q = n)
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)} (hz : IsFundamentalClass z) :
    ∃ x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S),
      IsFundamentalClass x ∧
        (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
            (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
          TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
            (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
              (𝟙_ (ModuleCat.{w} k)) L r q n hn (o ⊗ₜ x)) ∧
        ∀ (j q' m : ℕ) (hq : j + q' = q) (hm : r + q' = m) (hjm : j + m = n)
          (φ : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
            (𝟙_ (ModuleCat.{w} k)) j),
          (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
              (𝟙_ (ModuleCat.{w} k) ⊗ L) m
              ((TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
                (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z) =
            TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) m
              (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
                (𝟙_ (ModuleCat.{w} k)) L r q' m hm
                (o ⊗ₜ (((-1 : ℤ) ^ (r * j)) • (TopCat.of S).singularCap k (λ_ L).inv
                  (λ_ L).hom j q' q hq
                  (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ) x))) := by
  obtain ⟨x, hx, -⟩ :=
    h.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap L hf hr ho hn z
  refine ⟨x, h.isFundamentalClass_of_singularHomologyπ_eq L hr ho hn hx hz, hx, ?_⟩
  rintro j q' m rfl hm hjm φ
  exact h.singularHomologyπ_singularCap_eq L hr₀ hn hm hjm hx φ

end IsFramedTube

end TauCeti
