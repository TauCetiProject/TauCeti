/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.AbsoluteRelative
public import TauCeti.Geometry.Manifold.PontryaginThom.FundamentalClass
public import TauCeti.Geometry.Manifold.PontryaginThom.ThomCollapse
import TauCeti.AlgebraicTopology.Cohomology.Cap.CrossRel

/-!
# The shriek map of a framed submanifold and Poincaré duality

Let `τ : S × V → M` be a framed tube around `f : S → M` (`TauCeti.IsFramedTube`) with closed core
`f(S)`, with `V` a real normed space of dimension `r`, and let `o` generate the local homology
`H_r(V, V ∖ 0; k)`. The relative cross product with `o` followed by the tube is the Thom
isomorphism `H_q(S; L) ≃ H_{r+q}(M, M ∖ f(S); k ⊗ L)`, `x ↦ τ_*(o × x)`
(`TauCeti.IsFramedTube.homologyThomEquiv`, in
`TauCeti.Geometry.Manifold.PontryaginThom.FundamentalClass`).
The **shriek map**

`i_! : H_{r+q}(M; k ⊗ L) → H_q(S; L)`

of the framed submanifold (`TauCeti.IsFramedTube.shriek`) is the map to the homology relative to
the complement of the core, followed by the inverse of the Thom isomorphism: it sends `z` to the
unique class `x` with `z ↦ τ_*(o × x)` (`TauCeti.IsFramedTube.shriek_eq_iff`). It sends a
fundamental class `[M]` to a fundamental class `[S] = i_![M]` of `S`
(`TauCeti.IsFramedTube.isFundamentalClass_shriek`).

This file computes it in the two ways in which Barraud, Damian, Humilière and Oancea use it.

* **On cap products**, for `r ≠ 0`,

  `i_!(z ⌢ φ) = (-1)^(r j) i_!(z) ⌢ f^* φ`

  for `z ∈ H(M; k ⊗ L)` and `φ ∈ Hʲ(M; k)` (`TauCeti.IsFramedTube.shriek_singularCap`, from
  `TauCeti.IsFramedTube.singularHomologyπ_singularCap_eq`, which needs no closedness of the core).
  So when capping with `[M]` is a bijection `D_M`, as for the fundamental class of a closed
  oriented manifold (Poincaré duality,
  `TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`, stated in its
  own coefficient convention), the shriek map is
  `i_! = (-1)^(r j) D_S ∘ f^* ∘ D_M⁻¹` with `D_S` the cap product with `[S] = i_![M]`
  (`TauCeti.IsFramedTube.shriek_eq_singularCap_symm`).
* **Through the Thom space.** The Thom collapse `c : M → OnePoint (S × V)` onto the Thom space of
  the trivial bundle (`TauCeti.thomCollapse`) carries the tube of `M` onto the tube of the Thom
  space around its zero section, so `i_!` is `c_*` followed by the shriek map of the Thom space,
  the inverse of its Thom isomorphism `x ↦ o × x`
  (`TauCeti.IsFramedTube.shriek_map_thomCollapse`).

Together these say that the Poincaré duality form of the shriek map of a closed submanifold is the
map induced by its collapse onto the Thom space followed by the inverse of the suspension by `o`.

The codimension-zero case `r = 0` of the cap product formula is excluded: the computation inverts
the Thom isomorphism by the homology Thom map of
`TopCat.singularCap_singularHomologyCrossRel_of_isZero`, which is only available in positive degree.

The sign comes from the orientation convention: here `[M]` restricts along the core to `o × [S]`,
*the fibre followed by the core*. Barraud–Damian–Humilière–Oancea orient the core first
(Remark 9.2.4) and state the formula `i_! = D_S ∘ f^* ∘ D_M⁻¹` without a sign in that convention
(Proposition 11.3.2); the exchange of factors relating the two conventions is
`TauCeti.IsFramedTube.singularHomologyToLocalHomology_eq_neg_one_pow_smul`.

The cap product computation happens in the Thom pair `(V × S, (V ∖ 0) × S)` of the product bundle,
to which excision along the tube reduces it: there

`(o × x) ⌢ pr₂^* ψ = (-1)^(r j) o × (x ⌢ ψ)`

for `ψ ∈ Hʲ(S; k)` (`TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul`, in
`TauCeti.AlgebraicTopology.Cohomology.Cap.CrossRel`, where it is proved with the homology Thom
map and the projection formula `TopPair.map_singularCap_absoluteSingularCap`).

## Main results

* `TauCeti.IsFramedTube.isFundamentalClass_shriek`: `i_![M]` is a fundamental class of `S`.
* `TauCeti.IsFramedTube.singularHomologyπ_singularCap_eq`: if `z ↦ τ_*(o × x)`, then
  `z ⌢ φ ↦ τ_*(o × ((-1)^(r j) x ⌢ f^* φ))`.
* `TauCeti.IsFramedTube.shriek_singularCap`: `i_!(z ⌢ φ) = (-1)^(r j) i_!(z) ⌢ f^* φ`.
* `TauCeti.IsFramedTube.shriek_eq_singularCap_symm`: `i_! = (-1)^(r j) D_S ∘ f^* ∘ D_M⁻¹` when
  capping is bijective.
* `TauCeti.IsFramedTube.shriek_map_thomCollapse`: `i_!` is the Thom collapse followed by the
  shriek map of the Thom space.

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
tube of `o × ((-1)^(r j) x ⌢ f^* φ)`. When `finrank ℝ V = r`, `f(S)` is closed and `o` generates
the local homology, `x` is the image `i_!(z)` of `z` under the shriek map
(`TauCeti.IsFramedTube.shriek_eq_iff`), and this says `i_!(z ⌢ φ) = (-1)^(r j) i_!(z) ⌢ f^* φ`
(`TauCeti.IsFramedTube.shriek_singularCap`). -/
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

/-! ### The shriek map as a linear map -/

section ShriekMap

variable (h : IsFramedTube f τ) (hf : IsClosed (range f)) {r : ℕ} (hr : finrank ℝ V = r)
  (o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
    (C := ModuleCat.{w} k) (𝟙_ _) r) (ho : Submodule.span k {o} = ⊤)

/-- **The shriek map of a fundamental class is a fundamental class.** For a `T₁` space `M` and a
generator `o` of `H_r(V, V ∖ 0; k)` with `r = dim V`, the shriek map sends a fundamental class
`[M] ∈ H_n(M; k ⊗ L)` to a fundamental class `[S] = i_![M]` of `S`. -/
theorem isFundamentalClass_shriek [T1Space M] (q n : ℕ) (hn : r + q = n)
    {z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)} (hz : IsFundamentalClass z) :
    IsFundamentalClass (h.shriek L hf hr o ho q n hn z) :=
  h.isFundamentalClass_of_singularHomologyπ_eq L hr ho hn
    (h.singularHomologyπ_eq_shriek L hf hr o ho q n hn z) hz

/-- **The shriek map on cap products.** For `r = dim V ≠ 0`, the shriek map sends the cap product
`z ⌢ φ` of `z ∈ H_n(M; k ⊗ L)` with `φ ∈ Hʲ(M; k)` to `(-1)^(r j) i_!(z) ⌢ f^* φ`. The sign comes
from the orientation convention, the fibre followed by the core. -/
theorem shriek_singularCap (hr₀ : r ≠ 0) {j q m n : ℕ} (hn : r + (j + q) = n) (hm : r + q = m)
    (hjm : j + m = n)
    (φ : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)) :
    h.shriek L hf hr o ho q m hm
        ((TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
          (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z) =
      ((-1 : ℤ) ^ (r * j)) • (TopCat.of S).singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl
        (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j φ)
        (h.shriek L hf hr o ho (j + q) n hn z) :=
  (h.shriek_eq_iff L hf hr o ho q m hm _ _).2 (h.singularHomologyπ_singularCap_eq L hr₀ hn hm hjm
    (h.singularHomologyπ_eq_shriek L hf hr o ho (j + q) n hn z) φ)

/-- **The shriek map through Poincaré duality.** Let `r = dim V ≠ 0` and let `z ∈ H_n(M; k ⊗ L)`
be a class such that capping with it is a bijection `D : Hʲ(M; k) → H_m(M; k ⊗ L)`, as capping
with the fundamental class of a closed oriented manifold is (Poincaré duality,
`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`, in its own
coefficient convention). Then the shriek map is

`i_!(y) = (-1)^(r j) i_!(z) ⌢ f^* (D⁻¹ y)`.

For a fundamental class `z = [M]`, the class `i_![M]` is a fundamental class `[S]` of `S`
(`TauCeti.IsFramedTube.isFundamentalClass_shriek`), so this is
`i_! = (-1)^(r j) D_S ∘ f^* ∘ D_M⁻¹`, the form of the shriek map of Barraud–Damian–Humilière–Oancea
(Proposition 11.3.2), up to the sign of the orientation convention, the fibre followed by the
core. -/
theorem shriek_eq_singularCap_symm (hr₀ : r ≠ 0) {j q m n : ℕ} (hn : r + (j + q) = n)
    (hm : r + q = m) (hjm : j + m = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M))
    (hD : Function.Bijective fun φ : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) j ↦
      (TopCat.of M).singularCap k (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n hjm φ z)
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) m).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)) :
    h.shriek L hf hr o ho q m hm y =
      ((-1 : ℤ) ^ (r * j)) • (TopCat.of S).singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl
        (TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, h.continuous⟩) j
          ((Equiv.ofBijective _ hD).symm y))
        (h.shriek L hf hr o ho (j + q) n hn z) := by
  conv_lhs => rw [← Equiv.ofBijective_apply_symm_apply _ hD y]
  exact h.shriek_singularCap L hf hr o ho hr₀ hn hm hjm _ z

end ShriekMap

/-! ### The shriek map through the Thom space -/

section ThomCollapse

variable [CompactSpace S] [T2Space S] [T2Space M] (h : IsFramedTube f τ) {r : ℕ}
  (hr : finrank ℝ V = r)
  (o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
    (C := ModuleCat.{w} k) (𝟙_ _) r) (ho : Submodule.span k {o} = ⊤)

/-- **The shriek map factors through the Thom collapse.** Let `τ : S × V → M` be a framed tube
around a compact Hausdorff `S` in a Hausdorff space `M`, with `V` of dimension `r`, let `o`
generate `H_r(V, V ∖ 0; k)`, and let `c : M → OnePoint (S × V)` be the Thom collapse onto the Thom
space of the trivial bundle (`TauCeti.IsFramedTube.thomCollapseHom`). Then the shriek map of `M` is
the map `c_*` induced by the collapse followed by the shriek map of the Thom space along its zero
section, the inverse of the Thom isomorphism `x ↦ (o × x)` of the Thom space:
`i_! = (i_!)_{Th} ∘ c_*`. This is the suspension form of the factorization: the inverse Thom
isomorphism is the cross product with `o`, as opposed to the local homology of a Serre fibration
along the core in
`TauCeti.TopCat.singularHomologyπ_comp_singularHomologyComplPreimageCoreIso_hom`. -/
theorem shriek_map_thomCollapse (q n : ℕ) (hn : r + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k) ⊗ L)).obj
      (TopCat.of M)) :
    (isFramedTube_onePoint_coe (S := S) (V := V)).shriek L
        isFramedTube_onePoint_coe.isClosed_range hr o ho q n hn
        (SSet.homologyMap (TopCat.toSSet.map (h.thomCollapseHom (B := TopCat.of M)))
          (𝟙_ (ModuleCat.{w} k) ⊗ L) n z) =
      h.shriek L h.isClosed_range hr o ho q n hn z := by
  refine (isFramedTube_onePoint_coe.shriek_eq_iff L _ hr o ho q n hn _ _).2 ?_
  -- The collapse is a map of pairs `(M, M ∖ f(S)) → (Th, Th ∖ S)`, which carries the tube of `M`
  -- onto the tube of the Thom space.
  let C := TopPair.ofSubsetMap (X := TopCat.of M) (Y := TopCat.of (OnePoint (S × V)))
    (B := (range f)ᶜ) (B' := (range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ)
    (h.thomCollapseHom (B := TopCat.of M)) fun _ hm hc ↦
      hm (h.thomCollapse_mem_range_iff.1 (h.thomCollapseHom_apply (B := TopCat.of M) _ ▸ hc))
  have htube : h.tubePairMap ≫ C = (isFramedTube_onePoint_coe (S := S) (V := V)).tubePairMap := by
    rw [tubePairMap_def, tubePairMap_def]
    refine TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _
      (ConcreteCategory.hom_ext _ _ fun p ↦ ?_)
    simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, tubeMap_apply]
    exact (h.thomCollapseHom_apply (B := TopCat.of M) _).trans
      (thomCollapse_apply h.isOpenEmbedding.injective _)
  have hπ := ConcreteCategory.congr_hom
    (TopPair.singularHomologyπ_naturality C (𝟙_ (ModuleCat.{w} k) ⊗ L) n) z
  have hC : TopPair.Hom.fst C = h.thomCollapseHom (B := TopCat.of M) :=
    TopPair.ofSubsetMap_fst _ _
  rw [hC] at hπ
  -- The ambient object of each pair is the space only up to unfolding, so the composites are
  -- applied by unification rather than by `rw`.
  refine (ConcreteCategory.comp_apply _ _ z).symm.trans
    (hπ.trans ((ConcreteCategory.comp_apply _ _ z).trans ?_))
  refine (congrArg _ (h.singularHomologyπ_eq_shriek L h.isClosed_range hr o ho q n hn z)).trans ?_
  rw [← htube, TopPair.singularHomologyMap_comp]
  exact (ConcreteCategory.comp_apply _ _ _).symm

end ThomCollapse

end IsFramedTube

end TauCeti
