/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.AbsoluteRelative
public import TauCeti.Geometry.Manifold.PontryaginThom.FundamentalClass
import TauCeti.AlgebraicTopology.Cohomology.Cap.Pushforward
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross
import Mathlib.Analysis.Convex.Contractible

/-!
# The shriek map of a framed submanifold and Poincaré duality

Let `τ : S × V → M` be a framed tube around `f : S → M` (`TauCeti.IsFramedTube`) with closed core
`f(S)`, with `V` a real normed space of dimension `r`, and let `o` generate the local homology
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
(`TauCeti.IsFramedTube.exists_isFundamentalClass_forall_singularHomologyπ_singularCap_eq`). When
capping with `[M]` is bijective, as for a closed oriented manifold with integral coefficients
(`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`), this determines the
shriek map as `i_! = (-1)^(r j) D_S ∘ f^* ∘ D_M⁻¹`, with `D` the cap product with the fundamental
class.

The sign comes from the orientation convention: here `[M]` restricts along the core to `o × [S]`,
*the fibre followed by the core*. Barraud–Damian–Humilière–Oancea orient the core first
(Remark 9.2.4) and state the formula `i_! = D_S ∘ f^* ∘ D_M⁻¹` without a sign in that convention
(Proposition 11.3.2); the exchange of factors relating the two conventions is not used here.

The computation happens in the Thom pair `(V × S, (V ∖ 0) × S)` of the product bundle, to which
excision along the tube reduces it: there

`(o × x) ⌢ pr₂^* ψ = (-1)^(r j) o × (x ⌢ ψ)`

for `ψ ∈ Hʲ(S; k)` (`TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul`). Both sides are
linear in `o`, so it suffices to prove it for a generator `o`. Then choose the class
`u ∈ Hʳ(V, V ∖ 0; k)` with `⟨u, o⟩ = 1`
(`TauCeti.exists_singularKronecker_complSingleton_eq_one`). The homology Thom map
`a ↦ pr₂_*(a ⌢ pr₁^* u)` is a left inverse of `x ↦ o × x`
(`TopCat.singularCap_singularHomologyCrossRel_of_isZero`), which is bijective
(`TauCeti.bijective_singularHomologyCrossRel_tmul_complSingleton`), and it is linear over the
cohomology of `S` up to the sign `(-1)^(r j)`, by the projection formula
(`TopPair.map_singularCap_absoluteSingularCap`).

## Main results

* `TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul`:
  `(o × x) ⌢ pr₂^* ψ = (-1)^(r j) o × (x ⌢ ψ)` on the Thom pair of a product bundle.
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

/-- The case of `TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul` where `o` generates the
local homology of `V` at `0` and `V` has dimension `p + 1`. -/
private theorem absoluteSingularCap_singularHomologyCrossRel_tmul_of_span_eq_top (Y : TopCat.{w})
    {p j q n m : ℕ} (hr : finrank ℝ V = p + 1)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)} (ho : Submodule.span k {o} = ⊤)
    (hn : p + 1 + (j + q) = n) (hm : p + 1 + q = m) (h : j + m = n)
    (ψ : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj L).obj Y) :
    (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n h
        (TopCat.singularCohomologyMap (snd (TopCat.of V) Y :
          (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).fst ⟶ Y) j ψ)
        (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) (j + q) n hn (o ⊗ₜ x)) =
      ((-1 : ℤ) ^ ((p + 1) * j)) •
        TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) q m hm (o ⊗ₜ Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl ψ x) := by
  obtain rfl : m = p + q + 1 := by omega
  obtain rfl : n = p + (j + q) + 1 := by omega
  -- The class `u ∈ Hᵖ⁺¹(V, V ∖ 0; k)` with `⟨u, o⟩ = 1`.
  have hx : (0 : V) ∈ (OpenPartialHomeomorph.refl V).source := mem_univ _
  obtain ⟨u, huo⟩ := exists_singularKronecker_complSingleton_eq_one
    (OpenPartialHomeomorph.refl V) hx hr ho
  -- The homology Thom map `a ↦ pr₂_*(a ⌢ pr₁^* u)` is a left inverse of `y ↦ o × y`.
  have : ContractibleSpace (TopCat.of V) := inferInstanceAs (ContractibleSpace V)
  have hX := isZero_singularCohomology_of_contractibleSpace (𝟙_ (ModuleCat.{w} k)) k
    (𝟙_ (ModuleCat.{w} k)) (TopCat.of V) (n := p + 1) (by omega)
  have hΦ (q' : ℕ) (y : ((singularHomologyFunctor (ModuleCat.{w} k) q').obj L).obj Y) :=
    (TopCat.singularCap_singularHomologyCrossRel_of_isZero hX u o y).trans
      (by rw [huo, one_smul])
  -- Write the left side as `o × b`, and compute `b` with the Thom map.
  obtain ⟨b, hb⟩ := (bijective_singularHomologyCrossRel_tmul_complSingleton
    (OpenPartialHomeomorph.refl V) hx Y L hr ho q (p + q + 1) hm).2
    ((TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j (p + q + 1)
        (p + (j + q) + 1) h (TopCat.singularCohomologyMap (snd (TopCat.of V) Y :
          (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).fst ⟶ Y) j ψ)
        (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) (j + q) (p + (j + q) + 1) hn (o ⊗ₜ x)))
  beta_reduce at hb
  have hb' : b = ((-1 : ℤ) ^ ((p + 1) * j)) • Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q)
      rfl ψ x := by
    refine (hΦ q b).symm.trans ?_
    rw [hb]
    have hpf := TopPair.map_singularCap_absoluteSingularCap
      (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)) (𝟙 (𝟙_ (ModuleCat.{w} k) ⊗ L))
      (snd (TopCat.of V) Y) h hm hn rfl
      (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst (TopCat.of V) Y)
        (mapsTo_preimage _ _) : TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ) ⟶
          TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ) (p + 1) u) ψ
      (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L (p + 1)
        (j + q) (p + (j + q) + 1) hn (o ⊗ₜ x))
    -- In `hΦ` the push-forward along `snd` has source `TopCat.of V ⊗ Y`, in `hpf` the ambient
    -- space `(TopPair.ofSubset _).fst` of the pair; the two agree only up to unfolding
    -- `TopPair.ofSubset`, so the rewrite needs `erw`.
    erw [hΦ (j + q) x] at hpf
    exact hpf
  rw [← hb, hb', TensorProduct.tmul_smul, map_zsmul]

/-- **Capping the Thom isomorphism of a product bundle with a class of the base.** Let `V` be a
finite-dimensional real normed space, `o ∈ Hₚ₊₁(V, V ∖ 0; k)`, `Y` a space, `x ∈ H_{j+q}(Y; L)`
and `ψ ∈ Hʲ(Y; k)`. In the Thom pair `(V × Y, (V ∖ 0) × Y)` of the product bundle, capping the
relative cross product `o × x` with the pull-back `pr₂^* ψ` of `ψ` along the projection to `Y` is
`(-1)^((p + 1) j)` times the cross product of `o` with `x ⌢ ψ`. -/
theorem absoluteSingularCap_singularHomologyCrossRel_tmul (Y : TopCat.{w}) {p j q n m : ℕ}
    (hn : p + 1 + (j + q) = n) (hm : p + 1 + q = m) (h : j + m = n)
    (o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1))
    (ψ : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj L).obj Y) :
    (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n h
        (TopCat.singularCohomologyMap (snd (TopCat.of V) Y :
          (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).fst ⟶ Y) j ψ)
        (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) (j + q) n hn (o ⊗ₜ x)) =
      ((-1 : ℤ) ^ ((p + 1) * j)) •
        TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) q m hm (o ⊗ₜ Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl ψ x) := by
  have hx : (0 : V) ∈ (OpenPartialHomeomorph.refl V).source := mem_univ _
  by_cases hr : finrank ℝ V = p + 1
  · -- Both sides are linear in `o`, a multiple of a generator of the local homology.
    obtain ⟨g, hg⟩ := exists_span_singularHomology_complSingleton_eq_top
      (OpenPartialHomeomorph.refl V) hx (k := k) hr
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hg ▸ Submodule.mem_top (x := o))
    rw [← TensorProduct.smul_tmul', map_smul, map_smul,
      absoluteSingularCap_singularHomologyCrossRel_tmul_of_span_eq_top L Y hr hg hn hm h ψ x,
      ← TensorProduct.smul_tmul', map_smul, smul_comm]
  · -- Otherwise the local homology vanishes in degree `p + 1`, so `o = 0`.
    have := ModuleCat.subsingleton_of_isZero (isZero_singularHomology_complSingleton_of_ne
      (𝟙_ (ModuleCat.{w} k)) (OpenPartialHomeomorph.refl V) hx rfl (Ne.symm hr))
    rw [Subsingleton.elim o 0, TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero,
      map_zero, map_zero, smul_zero]

namespace IsFramedTube

variable {S M : Type w} [TopologicalSpace S] [TopologicalSpace M] {f : S → M} {τ : S × V → M}

/-- **The shriek map of a framed submanifold on cap products.** Let `τ : S × V → M` be a framed
tube around `f`, with `V` finite-dimensional, and let `o ∈ Hₚ₊₁(V, V ∖ 0; k)`. If the image of
`z ∈ H(M; k ⊗ L)` in `H(M, M ∖ f(S))` is the image under the tube of `o × x`, for
`x ∈ H_{j+q}(S; L)`, then for every `φ ∈ Hʲ(M; k)` the image of `z ⌢ φ` is the image under the
tube of `o × ((-1)^((p + 1) j) x ⌢ f^* φ)`. When `o` generates the local homology, `x` is the image
`i_!(z)` of `z` under the shriek map, and this says
`i_!(z ⌢ φ) = (-1)^((p + 1) j) i_!(z) ⌢ f^* φ`. -/
theorem singularHomologyπ_singularCap_eq (h : IsFramedTube f τ) {p j q n m : ℕ}
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)}
    (hn : p + 1 + (j + q) = n) (hm : p + 1 + q = m) (hjm : j + m = n)
    {x : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj L).obj (TopCat.of S)}
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)}
    (hz : (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L (p + 1) (j + q) n hn (o ⊗ₜ x)))
    (φ : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j) :
    (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
        (𝟙_ (ModuleCat.{w} k) ⊗ L) m
        ((TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
          (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z) =
      TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) m
        (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
          (𝟙_ (ModuleCat.{w} k)) L (p + 1) q m hm
          (o ⊗ₜ (((-1 : ℤ) ^ ((p + 1) * j)) • (TopCat.of S).singularCap k (λ_ L).inv (λ_ L).hom
            j q (j + q) rfl
            (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ) x))) := by
  -- Capping commutes with the map to the relative homology and with the tube, which pulls `φ`
  -- back to `pr₂^* f^* φ`.
  refine (ConcreteCategory.comp_apply _ _ z).symm.trans ?_
  refine (ConcreteCategory.congr_hom (TopPair.singularHomologyπ_comp_absoluteSingularCap
    (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ) k _ _ j m n hjm φ).symm z).trans ?_
  refine ((ConcreteCategory.comp_apply _ _ z).trans (congrArg _ hz)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  refine (ConcreteCategory.congr_hom (TopPair.absoluteSingularCap_naturality h.tubePairMap k
    _ _ j m n hjm φ).symm _).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ ?_)
  rw [h.singularCohomologyMap_tubePairMap]
  -- The pull-back along the composite is the pull-back along `snd` of the pull-back along `f`;
  -- `ConcreteCategory.comp_apply` does not rewrite it, as the source of `snd` is the ambient space
  -- of the pair only up to unfolding, so the step is taken by unification.
  refine (absoluteSingularCap_singularHomologyCrossRel_tmul L (TopCat.of S) hn hm hjm o _
    x).trans ?_
  rw [TensorProduct.tmul_smul, map_zsmul]
  -- The pull-back of `φ` along `f` appears once as `ModuleCat.Hom.hom'`, from the composite, and
  -- once as `ConcreteCategory.hom`; the two are equal by definition.
  rfl

/-- **The shriek map of a framed submanifold through Poincaré duality.** Let `τ : S × V → M` be a
framed tube around `f` with closed core, in a `T₁` space `M`, with `V` of dimension `p + 1`, and let
`o` generate `Hₚ₊₁(V, V ∖ 0; k)`. A fundamental class `[M] ∈ H_{p+1+q}(M; k ⊗ L)` induces a
fundamental class `[S] ∈ H_q(S; L)`, the image of `[M]` under the shriek map `i_!`, and `i_!` sends
the Poincaré dual `[M] ⌢ φ` of every class `φ ∈ Hʲ(M; k)` to `(-1)^((p + 1) j)` times the Poincaré
dual `[S] ⌢ f^* φ` of its restriction to `S`. For closed oriented `M`, where capping with `[M]` is
bijective, this determines `i_!` as `(-1)^((p + 1) j) D_S ∘ f^* ∘ D_M⁻¹`. -/
theorem exists_isFundamentalClass_forall_singularHomologyπ_singularCap_eq [T1Space M]
    (h : IsFramedTube f τ) (hf : IsClosed (range f)) {p q n : ℕ} (hr : finrank ℝ V = p + 1)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)} (ho : Submodule.span k {o} = ⊤)
    (hn : p + 1 + q = n)
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)} (hz : IsFundamentalClass z) :
    ∃ x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj L).obj (TopCat.of S),
      IsFundamentalClass x ∧
        (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
            (𝟙_ (ModuleCat.{w} k) ⊗ L) n z =
          TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) n
            (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
              (𝟙_ (ModuleCat.{w} k)) L (p + 1) q n hn (o ⊗ₜ x)) ∧
        ∀ (j q' m : ℕ) (hq : j + q' = q) (hm : p + 1 + q' = m) (hjm : j + m = n)
          (φ : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
            (𝟙_ (ModuleCat.{w} k)) j),
          (TopPair.ofSubset (X := TopCat.of M) (range f)ᶜ).singularHomologyπ
              (𝟙_ (ModuleCat.{w} k) ⊗ L) m
              ((TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
                (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z) =
            TopPair.singularHomologyMap h.tubePairMap (𝟙_ (ModuleCat.{w} k) ⊗ L) m
              (TopCat.singularHomologyCrossRel (TopCat.of V) (TopCat.of S) {(0 : V)}ᶜ
                (𝟙_ (ModuleCat.{w} k)) L (p + 1) q' m hm
                (o ⊗ₜ (((-1 : ℤ) ^ ((p + 1) * j)) • (TopCat.of S).singularCap k (λ_ L).inv
                  (λ_ L).hom j q' q hq
                  (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ) x))) := by
  obtain ⟨x, hx, -⟩ :=
    h.existsUnique_singularHomologyπ_eq_singularHomologyMap_tubePairMap L hf hr ho hn z
  refine ⟨x, h.isFundamentalClass_of_singularHomologyπ_eq L hr ho hn hx hz, hx, ?_⟩
  rintro j q' m rfl hm hjm φ
  exact h.singularHomologyπ_singularCap_eq L hn hm hjm hx φ

end IsFramedTube

end TauCeti
