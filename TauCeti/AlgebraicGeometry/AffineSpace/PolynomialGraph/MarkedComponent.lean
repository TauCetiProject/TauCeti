/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import TauCeti.AlgebraicGeometry.AffineSpace.Line
public import TauCeti.AlgebraicGeometry.AffineSpace.PolynomialGraph.Basic
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.Connected.Component
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# The marked component of a Kronecker graph pulled back along a chart

Let `k` be a field, `π : V ⟶ Spec k[X_0, …, X_{m-1}]` a morphism locally of finite type, and
`y : Spec k ⟶ V` a rational point with `π ∘ y` the origin. For a base `B ≠ 0` the graph
`a_B : Spec k[T] → Spec k[X_0, …, X_{m-1}]`, `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))`, of the
Kronecker substitution `MvPolynomial.polynomialGraph k m B` sends the origin to the origin, so `y`
and the origin of the line define a rational point `w = (y, 0)` of the fibre product
`W = V ×_{Spec k[X]} Spec k[T]`. The *marked component* is the connected component of `W` through
`w`. It is open and closed, because `W` is locally Noetherian, and is given its open subscheme
structure; it is affine when `V` is. Write `j` for its inclusion into `W`, and `g = pr_V ∘ j`,
`q = pr_{Spec k[T]} ∘ j`, and `c` for the lift of `w`, so that `g ∘ c = y` and `q ∘ c = 0`.

When `π` is étale (an *étale chart*), `q` is étale, so the marked component is smooth of relative
dimension one over `Spec k`, with `c` a section of its structure morphism, and it is integral,
being connected with regular local rings. If `π` maps the complement of `U ⊆ V` into a
hypersurface `V(h)` whose pullback `φ(h)` along `a_B` is nonzero, the principal open `D(φ(h))` of
the line pulls back into `g⁻¹(U)` (this step holds over any commutative ring), and `g⁻¹(U)` is a
nonempty dense open subset of the marked component, although `y` itself may lie outside `U`.

Taking the component through `w`, rather than all of `W`, matters: `W` can be disconnected even
when `V` is integral. Over `𝔽_3`, the chart `π(x, z) = (x, z² - 1 - 2x)` on `Spec 𝔽_3[x, z, z⁻¹]`
pulls the graph `T ↦ (T, T²)` back to `z² = (T + 1)²`, two disjoint copies of `D(T + 1)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.markedComponent`: the connected component of the fibre product
  through `(y, 0)`, as an open subscheme.
* `AlgebraicGeometry.Scheme.Hom.markedComponentPoint`: the lift `c` of `(y, 0)` to it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_markedComponent`: for an étale chart the
  marked component is smooth of relative dimension one over `Spec k`.
* `AlgebraicGeometry.Scheme.Hom.isIntegral_markedComponent`: for an étale chart it is integral.
* `AlgebraicGeometry.Scheme.Hom.preimage_snd_basicOpen_subset_preimage_fst`: the principal open
  `D(φ(h))` pulls back into the preimage of `U`.
* `AlgebraicGeometry.Scheme.Hom.nonempty_preimage_markedComponent`: for a universally open chart,
  such as an étale one, the preimage of `U` in the marked component is nonempty.
* `AlgebraicGeometry.Scheme.Hom.dense_preimage_markedComponent`: for an étale chart and open `U`,
  this preimage is dense.

## References

* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, proofs of Corollary 5.2.7 and Proposition 5.3.5, where a curve
  through a rational point of a smooth chart meeting a dense open set is needed.
* The Stacks Project, Lemma 33.25.4 (056T) and Properties, Lemma 28.7.7 (033N), for the
  integrality of a connected scheme smooth over a field.
-/

public section

noncomputable section

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry.Scheme.Hom

universe u

section CommRing

variable {R : Type u} [CommRing R] {m : ℕ} {V : Scheme.{u}}
  (π : V ⟶ Spec (.of (MvPolynomial (Fin m) R)))

/-- If `π` maps the complement of `U` into the hypersurface `V(h)`, then the principal open
`D(φ(h))` of the affine line, `φ` the base-`B` Kronecker substitution, pulls back into the
preimage of `U` in the fibre product: a point over `D(φ(h))` lies over a point of the graph
outside `V(h)`. -/
theorem preimage_snd_basicOpen_subset_preimage_fst (B : ℕ) {h : MvPolynomial (Fin m) R}
    {U : Set V} (hU : π '' Uᶜ ⊆ PrimeSpectrum.zeroLocus {h}) :
    pullback.snd π (Spec.map (CommRingCat.ofHom (polynomialGraph R m B))) ⁻¹'
        (PrimeSpectrum.basicOpen (polynomialGraph R m B h) : Set (PrimeSpectrum (Polynomial R))) ⊆
      pullback.fst π (Spec.map (CommRingCat.ofHom (polynomialGraph R m B))) ⁻¹' U := by
  intro x hx
  by_contra hxU
  have hx' := hU ⟨_, hxU, rfl⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Spec.map_apply] at hx'
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hx
    ((PrimeSpectrum.mem_zeroLocus _ _).mp hx' (Set.mem_singleton h))

end CommRing

section Field

variable {k : Type u} [Field k] {m : ℕ} {V : Scheme.{u}}
  (π : V ⟶ Spec (.of (MvPolynomial (Fin m) k))) [LocallyOfFiniteType π] {B : ℕ} (hB : B ≠ 0)
  (y : Spec (.of k) ⟶ V) (hy : y ≫ π = Spec.map (CommRingCat.ofHom constantCoeff))

/-- The point `(y, 0)` of the fibre product of `π` with the graph. -/
private def markedPullbackPoint :
    Spec (.of k) ⟶ pullback π (Spec.map (CommRingCat.ofHom (polynomialGraph k m B))) :=
  pullback.lift y (Spec.map (CommRingCat.ofHom Polynomial.constantCoeff))
    (by rw [hy, SpecMap_constantCoeff_comp_SpecMap_polynomialGraph hB])

/-- The **marked component**: for a chart `π : V ⟶ Spec k[X_0, …, X_{m-1}]`, a base `B ≠ 0` and a
rational point `y` of `V` over the origin, the connected component of the fibre product of `π` with
the graph `T ↦ (T, T ^ B, …, T ^ (B ^ (m - 1)))` through the point `(y, 0)`, with its open
subscheme structure. -/
def markedComponent :
    (pullback π (Spec.map (CommRingCat.ofHom (polynomialGraph k m B)))).Opens :=
  Scheme.connectedComponentOpen _ (markedPullbackPoint π hB y hy default)

private theorem coe_markedComponent_eq_connectedComponent :
    (π.markedComponent hB y hy : Set _) =
      connectedComponent (markedPullbackPoint π hB y hy default) :=
  Scheme.coe_connectedComponentOpen _ _

/-- The marked component is connected, and nonempty. -/
instance connectedSpace_markedComponent :
    ConnectedSpace (π.markedComponent hB y hy).toScheme :=
  inferInstanceAs (ConnectedSpace (Scheme.connectedComponentOpen _ _).toScheme)

/-- The marked component is closed as well as open in the fibre product. -/
instance isClosedImmersion_markedComponent_ι :
    IsClosedImmersion (π.markedComponent hB y hy).ι :=
  inferInstanceAs (IsClosedImmersion (Scheme.connectedComponentOpen _ _).ι)

/-- The marked component of a chart with affine source is affine, being closed in the affine fibre
product. -/
instance isAffine_markedComponent [IsAffine V] : IsAffine (π.markedComponent hB y hy).toScheme :=
  isAffine_of_isAffineHom (π.markedComponent hB y hy).ι

/-- The marked point `(y, 0)`, as a rational point of the marked component. -/
def markedComponentPoint : Spec (.of k) ⟶ (π.markedComponent hB y hy).toScheme :=
  IsOpenImmersion.lift (π.markedComponent hB y hy).ι (markedPullbackPoint π hB y hy) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, coe_markedComponent_eq_connectedComponent,
      Subsingleton.elim x default]
    exact mem_connectedComponent)

@[reassoc]
private theorem markedComponentPoint_ι :
    π.markedComponentPoint hB y hy ≫ (π.markedComponent hB y hy).ι =
      markedPullbackPoint π hB y hy :=
  IsOpenImmersion.lift_fac _ _ _

/-- The marked point lies over `y` in `V`. -/
@[reassoc (attr := simp)]
theorem markedComponentPoint_ι_fst :
    π.markedComponentPoint hB y hy ≫ (π.markedComponent hB y hy).ι ≫ pullback.fst _ _ = y := by
  rw [markedComponentPoint_ι_assoc, markedPullbackPoint, pullback.lift_fst]

/-- The marked point lies over the origin of the affine line. -/
@[reassoc (attr := simp)]
theorem markedComponentPoint_ι_snd :
    π.markedComponentPoint hB y hy ≫ (π.markedComponent hB y hy).ι ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom Polynomial.constantCoeff) := by
  rw [markedComponentPoint_ι_assoc, markedPullbackPoint, pullback.lift_snd]

/-- The marked component is the connected component of the fibre product through the image of the
marked point. -/
theorem coe_markedComponent :
    (π.markedComponent hB y hy : Set _) =
      connectedComponent
        ((π.markedComponent hB y hy).ι (π.markedComponentPoint hB y hy default)) := by
  rw [← Scheme.Hom.comp_apply, markedComponentPoint_ι, coe_markedComponent_eq_connectedComponent]

/-- The two structure morphisms of the marked component to `Spec k`, through the chart and through
the affine line, agree. -/
@[reassoc]
theorem markedComponent_ι_fst_comp_SpecMap_algebraMap :
    (π.markedComponent hB y hy).ι ≫ pullback.fst _ _ ≫ π ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin m) k))) =
      (π.markedComponent hB y hy).ι ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  rw [pullback.condition_assoc, SpecMap_polynomialGraph_comp_SpecMap_algebraMap]

/-- The marked point is a section of the structure morphism of the marked component to `Spec k`
through the affine line. -/
@[reassoc]
theorem markedComponentPoint_comp_SpecMap_algebraMap :
    π.markedComponentPoint hB y hy ≫ (π.markedComponent hB y hy).ι ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = 𝟙 _ := by
  rw [markedComponentPoint_ι_snd_assoc, SpecMap_constantCoeff_comp_SpecMap_algebraMap]

/-- For an étale chart the marked component is smooth of relative dimension one over `Spec k`,
through its étale projection to the affine line. -/
instance smoothOfRelativeDimension_markedComponent [Etale π] :
    SmoothOfRelativeDimension 1 ((π.markedComponent hB y hy).ι ≫ pullback.snd _ _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) :=
  inferInstanceAs (SmoothOfRelativeDimension (0 + (0 + 1)) _)

/-- For a universally open chart, such as an étale one, and `φ(h) ≠ 0`, with `φ` the base-`B`
Kronecker substitution, the marked component meets the preimage of the principal open `D(φ(h))` of
the affine line: its projection to the line is open and nonempty, and the line is irreducible. -/
theorem nonempty_preimage_basicOpen_markedComponent [UniversallyOpen π]
    {h : MvPolynomial (Fin m) k} (hh : polynomialGraph k m B h ≠ 0) :
    (((π.markedComponent hB y hy).ι ≫ pullback.snd _ _) ⁻¹'
      (PrimeSpectrum.basicOpen (polynomialGraph k m B h) :
        Set (PrimeSpectrum (Polynomial k)))).Nonempty :=
  ((π.markedComponent hB y hy).ι ≫ pullback.snd _ _).isOpenMap.denseRange_of_isPreirreducibleSpace
    |>.exists_mem_open (PrimeSpectrum.basicOpen _).isOpen
      ⟨(⊥ : PrimeSpectrum (Polynomial k)), (PrimeSpectrum.mem_basicOpen _ _).mpr hh⟩

/-- If the universally open chart `π`, such as an étale one, maps the complement of `U` into a
hypersurface `V(h)` with `φ(h) ≠ 0`, `φ` the base-`B` Kronecker substitution, then the preimage of
`U` in the marked component is nonempty. The marked point itself need not lie in it. -/
theorem nonempty_preimage_markedComponent [UniversallyOpen π] {h : MvPolynomial (Fin m) k}
    {U : Set V} (hU : π '' Uᶜ ⊆ PrimeSpectrum.zeroLocus {h}) (hh : polynomialGraph k m B h ≠ 0) :
    (((π.markedComponent hB y hy).ι ≫ pullback.fst _ _) ⁻¹' U).Nonempty :=
  (π.nonempty_preimage_basicOpen_markedComponent hB y hy hh).mono fun _ hx ↦
    π.preimage_snd_basicOpen_subset_preimage_fst B hU hx

variable [Etale π]

/-- The marked component of an étale chart is integral: it is connected, locally
Noetherian, and smooth over `k`, hence has regular local rings. -/
instance isIntegral_markedComponent : IsIntegral (π.markedComponent hB y hy).toScheme :=
  have := SmoothOfRelativeDimension.smooth 1 ((π.markedComponent hB y hy).ι ≫ pullback.snd _ _ ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  have : ∀ x, IsRegularLocalRing ((π.markedComponent hB y hy).toScheme.presheaf.stalk x) :=
    TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth
      ((π.markedComponent hB y hy).ι ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _

/-- If the étale chart `π` maps the complement of an open `U` into a hypersurface
`V(h)` with `φ(h) ≠ 0`, `φ` the base-`B` Kronecker substitution, then the preimage of `U` is a
nonempty, hence dense, open subset of the irreducible marked component. -/
theorem dense_preimage_markedComponent {h : MvPolynomial (Fin m) k} {U : V.Opens}
    (hU : π '' (U : Set V)ᶜ ⊆ PrimeSpectrum.zeroLocus {h}) (hh : polynomialGraph k m B h ≠ 0) :
    Dense (((π.markedComponent hB y hy).ι ≫ pullback.fst _ _) ⁻¹' U) :=
  (U.isOpen.preimage (Scheme.Hom.continuous _)).dense
    (π.nonempty_preimage_markedComponent hB y hy hU hh)

end Field

end AlgebraicGeometry.Scheme.Hom
