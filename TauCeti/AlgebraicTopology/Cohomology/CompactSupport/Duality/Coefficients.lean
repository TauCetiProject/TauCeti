/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.RestrictScalars
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.IntersectionForm
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.CapDuality
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod
public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

import TauCeti.CategoryTheory.Linear.Int

/-!
# Poincaré duality for an oriented closed manifold with coefficients in a ring

Let `M` be a compact Hausdorff manifold of dimension `n` with a homological orientation `o`, and
let `k` be a commutative ring. The fundamental class over `k`,
`[M]_k = TauCeti.HomologicalOrientation.fundamentalClassOver k`, is the image of the integral
fundamental class `[M]` in `Hₙ(M; k)` under the change of coefficients `ℤ → k`
(`TopCat.restrictScalarsHomologyMap`), where homology and cohomology over `k` are formed from
singular chains over `k`. This file proves Poincaré duality over `k`: capping with `[M]_k` is a
bijection `Hᵖ(M; k) → H_q(M; k)` for `p + q = n`
(`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClassOver`).

The integral theorem `TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`
already gives duality with coefficients in any abelian group, for integral chains; here the
coefficient group is `k`. Restricting cochains over `k` to integral chains is an isomorphism of
cochain complexes, singular homology commutes with restriction of scalars, and the cap product is
compatible with both comparisons (`TopCat.restrictScalarsHomologyMap_comp_map_singularCap`), so the
cap product with `[M]_k` is the integral duality isomorphism between the comparisons.

Over a field `k` this makes the cup pairing `(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` of `Hᵖ(M; k)` with
`H^q(M; k)` nondegenerate
(`TauCeti.HomologicalOrientation.nondegenerate_singularCupPairing_fundamentalClassOver`),
by the duality between cap products and the cup pairing over a field. For an ordered field and
`n = 2p + d + 1` with `p + d + 1` even, this discharges the nondegeneracy hypothesis of the
computation of the indices of inertia of the cup pairing on `Sᵈ⁺¹ × M` against `[Sᵈ⁺¹] × [M]_k`:
both are `dim Hᵖ(M; k)`
(`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_fundamentalClassOver` and
`TauCeti.HomologicalOrientation.sigNeg_singularCupPairing_sphere_fundamentalClassOver`).
For a closed oriented three-manifold `Y` with finite-dimensional real cohomology, `k = ℝ`, `d = 0`
and `p = 1`, this is `b₂⁺ = b₂⁻ = b₁(Y)` for the real cup pairing of `S¹ × Y` against
`[S¹] × [Y]_ℝ`.

A map `f : M → N` of compact oriented `n`-manifolds with `N` preconnected carries `[M]_k` to
`deg f • [N]_k` (`TauCeti.HomologicalOrientation.map_fundamentalClassOver_eq_degree_smul`), so by
naturality of the cup pairing `⟨f^*α ⌣ f^*β, [M]_k⟩ = deg f • ⟨α ⌣ β, [N]_k⟩`
(`singularCupPairing_singularCohomologyMap_fundamentalClassOver_eq_degree_smul`).
In particular a self-map of degree one, such as an orientation-preserving homeomorphism, is an
isometry of the cup pairing on the middle cohomology
(`TauCeti.HomologicalOrientation.isIsometry_singularCohomologyMap_of_degree_eq_one`). On a closed
oriented surface over a field with `2 ≠ 0` that pairing on `H¹(M; k)` is nondegenerate and
alternating, so the action of such a map on `H¹(M; k)` is symplectic.

**The fundamental class of `Sᵈ⁺¹ × M`.** Over a field, `[M]_k` is nonzero on a nonempty `M`, since
the unit of `H⁰(M; k)` pairs nontrivially against it
(`TauCeti.HomologicalOrientation.fundamentalClassOver_ne_zero`), so on a connected `M` it is a
fundamental class (`TauCeti.HomologicalOrientation.isFundamentalClass_fundamentalClassOver`). For
connected `M`, the cross product `[Sᵈ⁺¹] × [M]_k` is then a fundamental class of the connected
product (`TauCeti.IsFundamentalClass.singularHomologyTopCatSphereGenerator_singularHomologyCross`),
and every top class of the product is a unique multiple of it. So for every homological orientation
of `Sᵈ⁺¹ × M`, whatever its manifold structure, its fundamental class over `k` is a nonzero multiple
`c ([Sᵈ⁺¹] × [M]_k)`
(`HomologicalOrientation.exists_ne_zero_fundamentalClassOver_eq_smul_singularHomologyCross`).
Scaling the cup pairing by `c` keeps or exchanges its two indices of inertia, according to the sign
of `c`, and these are equal. Hence both indices of inertia of the cup pairing against
`[Sᵈ⁺¹ × M]_k` are `dim Hᵖ(M; k)`
(`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_prod_fundamentalClassOver`,
`TauCeti.HomologicalOrientation.sigNeg_singularCupPairing_sphere_prod_fundamentalClassOver`). For a
closed connected oriented three-manifold `Y` with finite-dimensional real cohomology, `k = ℝ`,
`d = 0` and `p = 1`, this is `b₂⁺(S¹ × Y) = b₂⁻(S¹ × Y) = b₁(Y)` for the real intersection form of
either orientation of `S¹ × Y`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Theorem 3.30 and Proposition 3.38.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Module

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]

section CommRing

variable {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (k : Type)
  [CommRing k]

/-- **Poincaré duality with coefficients in a commutative ring.** For a compact Hausdorff manifold
`M` without boundary of dimension `n` with a homological orientation, and a commutative ring `k`,
capping with the fundamental class `[M]_k ∈ Hₙ(M; k)` over `k` is a bijection
`Hᵖ(M; k) → H_q(M; k)` for `p + q = n`, with homology and cohomology formed from singular chains
over `k`. -/
theorem bijective_singularCapLinearMap_fundamentalClassOver [CompactSpace M] {p q : ℕ}
    (h : p + q = n) :
    Function.Bijective ((TopCat.of M).singularCapLinearMap k h (o.fundamentalClassOver hn k)) := by
  -- The integral duality theorem is stated for the `ℤ`-linear structure of a preadditive
  -- category, the comparison for that of a category of modules; they agree by uniqueness.
  have hPD (_ : Linear ℤ (ModuleCat.{0} ℤ)) [MonoidalLinear ℤ (ModuleCat.{0} ℤ)] :
      Function.Bijective fun β : (TopCat.of M).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          ((ModuleCat.restrictScalars (Int.castRingHom k)).obj (𝟙_ (ModuleCat k))) p ↦
        ((TopCat.of M).singularCap ℤ (ρ_ _).inv (ρ_ _).hom p q n h β).hom
          (o.fundamentalClass hn) := by
    obtain rfl := Subsingleton.elim ‹Linear ℤ (ModuleCat.{0} ℤ)› Linear.preadditiveIntLinear
    exact (congrArg Function.Bijective (funext fun β ↦ TopCat.singularCapAddHom_apply ℤ
      (ρ_ _).inv (ρ_ _).hom (TopCat.of M) h (o.fundamentalClass hn) β)).mp
        (o.bijective_singularCapAddHom_fundamentalClass hn _ p q h)
  -- The two comparisons, read with the carriers of the cohomology and homology over `k`, which
  -- are those of their restrictions of scalars.
  have hT : Function.Bijective fun α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p ↦ (TopCat.of M).restrictScalarsCohomologyMap (Int.castRingHom k)
        (ModuleCat.uliftUnitToRestrictScalars _) p α :=
    ConcreteCategory.bijective_of_isIso ((TopCat.of M).restrictScalarsCohomologyMap
      (Int.castRingHom k) (ModuleCat.uliftUnitToRestrictScalars _) p)
  have hΘ : Function.Bijective fun x ↦ @id (((singularHomologyFunctor (ModuleCat k) q).obj
      (𝟙_ (ModuleCat k))).obj (TopCat.of M))
        ((TopCat.of M).restrictScalarsHomologyMap (Int.castRingHom k) (𝟙 _) q x) :=
    ConcreteCategory.bijective_of_isIso ((TopCat.of M).restrictScalarsHomologyMap
      (Int.castRingHom k) (𝟙 _) q)
  convert hΘ.comp ((hPD ModuleCat.instLinear).comp hT) using 1
  funext α
  rw [TopCat.singularCapLinearMap_apply, fundamentalClassOver_def]
  exact ConcreteCategory.congr_hom ((TopCat.of M).restrictScalarsHomologyMap_comp_map_singularCap
    (Int.castRingHom k) (ModuleCat.uliftUnitToRestrictScalars _) p q n h α) (o.fundamentalClass hn)

end CommRing

section Field

variable {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) {k : Type} [Field k]

/-- **The cup pairing of a closed oriented manifold over a field is nondegenerate**: for a compact
Hausdorff manifold `M` of dimension `n` with a homological orientation and a field `k`, the cup
pairing `(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` of `Hᵖ(M; k)` with `H^q(M; k)`, `p + q = n`, is nondegenerate. -/
theorem nondegenerate_singularCupPairing_fundamentalClassOver [CompactSpace M] {p q : ℕ}
    (h : p + q = n) :
    ((TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k)).Nondegenerate :=
  ⟨((TopCat.of M).injective_singularCapLinearMap_iff k h _).1
      (o.bijective_singularCapLinearMap_fundamentalClassOver hn k h).1,
    ((TopCat.of M).separatingRight_singularCupPairing_iff k h (by omega) _).2
      (o.bijective_singularCapLinearMap_fundamentalClassOver hn k (by omega)).1⟩

/-- **The fundamental class over a field is nonzero** on a nonempty compact oriented manifold: a
nonzero class of `H⁰(M; k)`, such as the constant function `1`, pairs nontrivially with some class
against `[M]_k` by Poincaré duality. -/
theorem fundamentalClassOver_ne_zero [CompactSpace M] [Nonempty M] (k : Type) [Field k] :
    o.fundamentalClassOver hn k ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := exists_singularCohomologyZeroEval_eq (X := TopCat.of M) (k := k)
    (fun _ ↦ 1) fun _ _ _ ↦ rfl
  have hu0 : u = 0 := (o.nondegenerate_singularCupPairing_fundamentalClassOver hn (k := k)
    (p := 0) (q := n) (by omega)).1 u fun β ↦ by rw [h0]; simp
  obtain ⟨x⟩ := ‹Nonempty M›
  simpa [hu0] using hu x

/-- **The fundamental class over a field is a fundamental class**: on a compact connected oriented
manifold, the image `[M]_k` of the integral fundamental class generates the local homology
`Hₙ(M, M ∖ {x}; k)` at every point `x`. -/
theorem isFundamentalClass_fundamentalClassOver [CompactSpace M] [ConnectedSpace M] (k : Type)
    [Field k] : IsFundamentalClass (o.fundamentalClassOver hn k) :=
  have : Nonempty M := ConnectedSpace.toNonempty
  (isFundamentalClass_iff_ne_zero hn _).2 (o.fundamentalClassOver_ne_zero hn k)

end Field

section Degree

variable {N F : Type} [TopologicalSpace N] [T2Space N] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [ChartedSpace F N] {n : ℕ} (o : HomologicalOrientation M E n)
  (o' : HomologicalOrientation N F n) (hn : finrank ℝ E = n) (k : Type) [CommRing k]
  [CompactSpace M]

/-- **The cup pairing under a map of degree `d`**: for a map `f : M → N` of compact oriented
`n`-manifolds with `N` preconnected, a commutative ring `k` and classes `α ∈ Hᵖ(N; k)`,
`β ∈ H^q(N; k)` with `p + q = n`, `⟨f^*α ⌣ f^*β, [M]_k⟩ = deg f • ⟨α ⌣ β, [N]_k⟩`. -/
theorem singularCupPairing_singularCohomologyMap_fundamentalClassOver_eq_degree_smul
    (hF : finrank ℝ F = n) [CompactSpace N] [PreconnectedSpace N] {p q : ℕ} (h : p + q = n)
    (f : C(M, N))
    (α : (TopCat.of N).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p)
    (β : (TopCat.of N).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) q) :
    (TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k)
        (TopCat.singularCohomologyMap (TopCat.ofHom f) p α)
        (TopCat.singularCohomologyMap (TopCat.ofHom f) q β) =
      o.degree o' hn f •
        (TopCat.of N).singularCupPairing k h (o'.fundamentalClassOver hF k) α β := by
  rw [TopCat.singularCupPairing_naturality, o.map_fundamentalClassOver_eq_degree_smul o' hn hF,
    TopCat.singularCupPairing_apply, TopCat.singularCupPairing_apply, map_zsmul]

/-- **A map of degree one preserves the middle cup pairing**: for a self-map `f` of degree one of
a compact connected oriented `n`-manifold, such as an orientation-preserving homeomorphism, and
`p + p = n`, the pull-back `f^*` on `Hᵖ(M; k)` is an isometry of the cup pairing
`(α, β) ↦ ⟨α ⌣ β, [M]_k⟩`. -/
theorem isIsometry_singularCohomologyMap_of_degree_eq_one [PreconnectedSpace M] {p : ℕ}
    (h : p + p = n) {f : C(M, M)} (hf : o.degree o hn f = 1) :
    BilinForm.IsIsometry ((TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k))
      (TopCat.singularCohomologyMap (TopCat.ofHom f) p).hom :=
  BilinForm.isIsometry_iff.2 fun α β ↦ by
    simpa [hf] using o.singularCupPairing_singularCohomologyMap_fundamentalClassOver_eq_degree_smul
      o hn k hn h f α β

end Degree

section Prod

/-! ### The fundamental class of `Sᵈ⁺¹ × M` -/

variable [CompactSpace M] [ConnectedSpace M] {n : ℕ} (o : HomologicalOrientation M E n)
  (hn : finrank ℝ E = n) {k : Type} [Field k] {d N : ℕ} {E' : Type} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' (TopCat.sphere.{0} (d + 1) × M)]
  (oX : HomologicalOrientation (TopCat.sphere.{0} (d + 1) × M) E' N) (hX : finrank ℝ E' = N)
  (h : d + 1 + n = N)

/-- **The fundamental class of `Sᵈ⁺¹ × M` over a field.** For a compact connected oriented manifold
`M` of dimension `n` and any homological orientation of the product `Sᵈ⁺¹ × M`, for any manifold
structure on it, the fundamental class `[Sᵈ⁺¹ × M]_k` over a field `k` is a nonzero multiple of the
cross product `[Sᵈ⁺¹] × [M]_k`, read with coefficients `k` through `k ⊗ k ≅ k`. -/
theorem exists_ne_zero_fundamentalClassOver_eq_smul_singularHomologyCross :
    ∃ c : k, c ≠ 0 ∧ oX.fundamentalClassOver hX k =
      c • ((singularHomologyFunctor (ModuleCat k) N).map
        (λ_ (𝟙_ (ModuleCat k))).hom).app (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)
        (TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
          (𝟙_ (ModuleCat k)) (𝟙_ (ModuleCat k)) (d + 1) n N h
          (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ o.fundamentalClassOver hn k)) := by
  subst h
  -- The cross product is a fundamental class of the product.
  have hcross : IsFundamentalClass (M := TopCat.sphere.{0} (d + 1) × M)
      ((TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
        (ModuleCat.of k k) (ModuleCat.of k k) (d + 1) n (d + 1 + n) rfl).hom
        (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ o.fundamentalClassOver hn k)) :=
    IsFundamentalClass.singularHomologyTopCatSphereGenerator_singularHomologyCross hn
      (o.isFundamentalClass_fundamentalClassOver hn k)
  have hz := (isFundamentalClass_singularHomologyFunctor_map_app_iff (λ_ (𝟙_ (ModuleCat k)))
    _).2 hcross
  -- On the connected product, every top class is a multiple of this fundamental class.
  obtain ⟨c, hc, -⟩ := hz.existsUnique_eq_smul hX (oX.fundamentalClassOver hX k)
  have : Nonempty (TopCat.sphere.{0} (d + 1) × M) := ConnectedSpace.toNonempty
  refine ⟨c, ?_, hc⟩
  rintro rfl
  exact oX.fundamentalClassOver_ne_zero hX k (hc.trans (zero_smul k _))

/-- The cup pairing against the fundamental class of `Sᵈ⁺¹ × M` is a nonzero multiple of the cup
pairing against `[Sᵈ⁺¹] × [M]_k`. -/
private theorem exists_ne_zero_singularCupPairing_fundamentalClassOver_eq_smul {i j : ℕ}
    (hij : i + j = N) :
    ∃ c : k, c ≠ 0 ∧ (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k hij
      (oX.fundamentalClassOver hX k) =
      c • (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k hij
        (((singularHomologyFunctor (ModuleCat k) N).map
          (λ_ (𝟙_ (ModuleCat k))).hom).app (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)
          (TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
            (𝟙_ (ModuleCat k)) (𝟙_ (ModuleCat k)) (d + 1) n N h
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ
              o.fundamentalClassOver hn k))) := by
  obtain ⟨c, hc0, hc⟩ :=
    o.exists_ne_zero_fundamentalClassOver_eq_smul_singularHomologyCross hn (k := k) oX hX h
  refine ⟨c, hc0, ?_⟩
  rw [hc]
  ext α β
  simp

end Prod

section Signature

variable {k : Type} [Field k] [CompactSpace M] {d p : ℕ}
  (o : HomologicalOrientation M E (p + p + (d + 1))) (hn : finrank ℝ E = p + p + (d + 1))

/-- The cup pairing of `Hᵖ⁺ᵈ⁺¹(M; k)` with `Hᵖ(M; k)` against `[M]_k` separates the classes of
`Hᵖ(M; k)`. -/
private theorem injective_flip_singularCupPairing_fundamentalClassOver :
    Function.Injective ((TopCat.of M).singularCupPairing k (p := p + (d + 1)) (q := p)
      (by omega) (o.fundamentalClassOver hn k)).flip :=
  LinearMap.ker_eq_bot.1 (LinearMap.separatingRight_iff_flip_ker_eq_bot.1
    (o.nondegenerate_singularCupPairing_fundamentalClassOver hn (by omega)).2)

variable [LinearOrder k] [IsStrictOrderedRing k]

/-- **The positive index of inertia of the cup pairing on `Sᵈ⁺¹ × M`**: for a compact oriented
manifold `M` of dimension `2p + d + 1` with `p + d + 1` even and an ordered field `k` over which
`Hᵖ⁺ᵈ⁺¹(M; k)` and `Hᵖ(M; k)` are finite dimensional, the cup pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × M; k)`
against `[Sᵈ⁺¹] × [M]_k` has positive index of inertia `dim Hᵖ(M; k)`. For a closed oriented
three-manifold `Y` with finite-dimensional real cohomology, `k = ℝ`, `d = 0` and `p = 1`, this gives
`b₂⁺ = b₁(Y)` for the real cup pairing of `S¹ × Y` against `[S¹] × [Y]_ℝ`; against the fundamental
class of `S¹ × Y` this is
`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_prod_fundamentalClassOver`. -/
theorem sigPos_singularCupPairing_sphere_fundamentalClassOver (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega)
        (((singularHomologyFunctor (ModuleCat k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat k))).hom).app (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)
          (TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
            (𝟙_ (ModuleCat k)) (𝟙_ (ModuleCat k)) (d + 1) (p + p + (d + 1))
            (p + p + (d + 1) + (d + 1)) (by omega)
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ
              o.fundamentalClassOver hn k))))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) :=
  TopCat.sigPos_singularCupPairing_sphere_singularHomologyCross_of_injective_flip hn (by omega)
    hp _ (o.injective_flip_singularCupPairing_fundamentalClassOver hn)

/-- **The negative index of inertia of the cup pairing on `Sᵈ⁺¹ × M`**: under the hypotheses of
`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_fundamentalClassOver`, the cup
pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × M; k)` against `[Sᵈ⁺¹] × [M]_k` has negative index of inertia
`dim Hᵖ(M; k)`. For a closed oriented three-manifold `Y` with finite-dimensional real cohomology,
`k = ℝ`, `d = 0` and `p = 1`, this gives `b₂⁻ = b₁(Y)` for the real cup pairing of `S¹ × Y` against
`[S¹] × [Y]_ℝ`; against the fundamental class of `S¹ × Y` this is
`TauCeti.HomologicalOrientation.sigNeg_singularCupPairing_sphere_prod_fundamentalClassOver`. -/
theorem sigNeg_singularCupPairing_sphere_fundamentalClassOver (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega)
        (((singularHomologyFunctor (ModuleCat k) (p + p + (d + 1) + (d + 1))).map
          (λ_ (𝟙_ (ModuleCat k))).hom).app (TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M)
          (TopCat.singularHomologyCross (TopCat.sphere.{0} (d + 1)) (TopCat.of M)
            (𝟙_ (ModuleCat k)) (𝟙_ (ModuleCat k)) (d + 1) (p + p + (d + 1))
            (p + p + (d + 1) + (d + 1)) (by omega)
            (TauCeti.singularHomologyTopCatSphereGenerator k d ⊗ₜ
              o.fundamentalClassOver hn k))))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) :=
  TopCat.sigNeg_singularCupPairing_sphere_singularHomologyCross_of_injective_flip hn (by omega)
    hp _ (o.injective_flip_singularCupPairing_fundamentalClassOver hn)

variable [ConnectedSpace M] {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [ChartedSpace E' (TopCat.sphere.{0} (d + 1) × M)]
  (oX : HomologicalOrientation (TopCat.sphere.{0} (d + 1) × M) E' (p + p + (d + 1) + (d + 1)))
  (hX : finrank ℝ E' = p + p + (d + 1) + (d + 1))

include o hn in
/-- **The positive index of inertia of the intersection form of `Sᵈ⁺¹ × M`.** For a compact
connected oriented manifold `M` of dimension `2p + d + 1` with `p + d + 1` even, an ordered field
`k` over which `Hᵖ⁺ᵈ⁺¹(M; k)` and `Hᵖ(M; k)` are finite dimensional, and any homological orientation
of `Sᵈ⁺¹ × M`, the cup pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × M; k)` against the fundamental class
`[Sᵈ⁺¹ × M]_k` has positive index of inertia `dim Hᵖ(M; k)`. For a closed connected oriented
three-manifold `Y` with finite-dimensional real cohomology, `k = ℝ`, `d = 0` and `p = 1`, this is
`b₂⁺(S¹ × Y) = b₁(Y)`, for either orientation of `S¹ × Y`. -/
theorem sigPos_singularCupPairing_sphere_prod_fundamentalClassOver (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigPos (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) (oX.fundamentalClassOver hX k))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_ne_zero_singularCupPairing_fundamentalClassOver_eq_smul o hn (k := k) oX hX
      (by omega) (i := p + (d + 1)) (j := p + (d + 1)) (by omega)
  rw [hc, LinearMap.BilinMap.toQuadraticMap_smul]
  rcases hc0.lt_or_gt with hneg | hpos
  · rw [QuadraticForm.sigPos_smul_of_neg _ hneg]
    exact o.sigNeg_singularCupPairing_sphere_fundamentalClassOver hn hp
  · rw [QuadraticForm.sigPos_smul_of_pos _ hpos]
    exact o.sigPos_singularCupPairing_sphere_fundamentalClassOver hn hp

include o hn in
/-- **The negative index of inertia of the intersection form of `Sᵈ⁺¹ × M`.** Under the
hypotheses of
`TauCeti.HomologicalOrientation.sigPos_singularCupPairing_sphere_prod_fundamentalClassOver`, the
cup pairing on `Hᵖ⁺ᵈ⁺¹(Sᵈ⁺¹ × M; k)` against `[Sᵈ⁺¹ × M]_k` has negative index of inertia
`dim Hᵖ(M; k)`. For a closed connected oriented three-manifold `Y` with finite-dimensional real
cohomology, `k = ℝ`, `d = 0` and `p = 1`, this is `b₂⁻(S¹ × Y) = b₁(Y)`. -/
theorem sigNeg_singularCupPairing_sphere_prod_fundamentalClassOver (hp : Even (p + (d + 1)))
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) (p + (d + 1)))]
    [FiniteDimensional k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) p)] :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      ((TopCat.sphere.{0} (d + 1) ⊗ TopCat.of M).singularCupPairing k (p := p + (d + 1))
        (q := p + (d + 1)) (by omega) (oX.fundamentalClassOver hX k))) =
      finrank k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) p) := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_ne_zero_singularCupPairing_fundamentalClassOver_eq_smul o hn (k := k) oX hX
      (by omega) (i := p + (d + 1)) (j := p + (d + 1)) (by omega)
  rw [hc, LinearMap.BilinMap.toQuadraticMap_smul]
  rcases hc0.lt_or_gt with hneg | hpos
  · rw [QuadraticForm.sigNeg_smul_of_neg _ hneg]
    exact o.sigPos_singularCupPairing_sphere_fundamentalClassOver hn hp
  · rw [QuadraticForm.sigNeg_smul_of_pos _ hpos]
    exact o.sigNeg_singularCupPairing_sphere_fundamentalClassOver hn hp

end Signature

end TauCeti.HomologicalOrientation
