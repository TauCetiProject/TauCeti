/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded.Contraction

/-!
# Cup products of classes of contracted complexes

Let `J₁`, `J₂` and `J₃` be complexes of topological representations of a locally compact group
`G`, contracted onto `X`, `Y` and `Z` by contractions that need not be equivariant
(`TopRep.ResolutionContraction`), so that an invariant cocycle of each has a class in continuous
cohomology through the comparison with the coinduced resolution. Let `μ : J₁ᵖ × J₂^q → J₃^{p+q}`
be an equivariant bilinear pairing with `d (a · b) = d a · b` whenever `b` is a cocycle, lying over
a coefficient pairing `P : X × Y → Z` in the following sense: multiplying on the left by an
augmented element `ι x` commutes with the contractions,

```text
proj (ι x · w) = P (x, proj w),        hom (ι x · w) = ι x · hom w.
```

Then the class of `a · b` is the cup product `[a] ⌣ [b]` for `P`
(`TopRep.ResolutionContraction.cohomologyClass_pairing`). The contracting homotopies are not
required to be multiplicative, which tensor products of contractions are not in general; only
compatibility with left multiplication by augmented elements is used. This is the tool for
identifying a product written on a resolution other than the coinduced one, such as the
factorwise cup pairing of the tensor-induced resolutions on which Evens' multiplicative transfer
is computed, with the canonical cup product.

The proof fixes `b`. Both `a ↦ comparison (a · b)` and `a ↦ comparison a ⌣ comparison b` are
equivariant maps from `J₁` to the coinduced resolution of `Z` raising degrees by `q` and commuting
with the differentials. On the augmentation they agree: the comparison of `ι x · w` is the
Alexander–Whitney product of the constant cochain `x` with the comparison of `w`
(`TopRep.ResolutionContraction.comparison_f_pairing_ι`). Two such maps are homotopic, by the
degree-by-degree extension `TopRep.ResolutionContraction.desc` of the comparison theorem, so they
carry an invariant cocycle to cohomologous cocycles
(`TopRep.ResolutionContraction.cochainClass_eq_of_ι_comp_eq`).

## Main results

* `TopRep.ResolutionContraction.comparison_f_pairing_ι`: the comparison of a left product with an
  augmented element is an Alexander–Whitney product.
* `TopRep.ResolutionContraction.cohomologyClass_pairing`: the class of a product of invariant
  cocycles is the cup product of their classes.
* `TopRep.ResolutionContraction.gradedCohomologyClass_pairing`: the same for a pairing of graded
  representations written on their total modules, such as tensor-induced total resolutions.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, for the cup
  product and its independence of the resolution.
* C. A. Weibel, *An Introduction to Homological Algebra*, Comparison Theorem 2.2.6 and its dual
  2.3.7.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. **108** (1963), §§2–6, for products on tensor-induced resolutions.
-/

public section

open CategoryTheory

namespace TopRep

universe u v w

variable {k : Type u} {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ResolutionContraction

section Pairing

variable [CommRing k] [TopologicalSpace k] {X Y Z : TopRep.{max v w} k G}
  {J₁ J₂ J₃ : CochainComplex (TopRep.{max v w} k G) ℕ}
  (c₁ : ResolutionContraction X J₁) (c₂ : ResolutionContraction Y J₂)
  (c₃ : ResolutionContraction Z J₃) (P : TauCeti.TopPairing X Y Z)
  (μ : ∀ p q, (J₁.X p).V →ₗ[k] (J₂.X q).V →ₗ[k] (J₃.X (p + q)).V)

/-- **The comparison of a left product with an augmented element.** Let `μ` pair the terms of
complexes contracted onto `X`, `Y` and `Z`, equivariantly, and suppose that multiplying on the
left by an augmented element `ι x` commutes with the contractions: the retraction of `ι x · w` is
`P (x, proj w)` and the contracting homotopy of `ι x · w` is `ι x · hom w`. Then the comparison
of `ι x · w` is the Alexander–Whitney product of the constant cochain `x` with the comparison of
`w`. -/
theorem comparison_f_pairing_ι
    (hρ : ∀ q g a b, μ 0 q ((J₁.X 0).ρ g a) ((J₂.X q).ρ g b) = (J₃.X (0 + q)).ρ g (μ 0 q a b))
    (hproj : ∀ x w, c₃.proj (μ 0 0 (c₁.ι.hom x) w) = P.bil x (c₂.proj w))
    (hhom : ∀ q x w,
      c₃.hom (0 + q) (μ 0 (q + 1) (c₁.ι.hom x) w) = μ 0 q (c₁.ι.hom x) (c₂.hom q w))
    (q : ℕ) (x : X.V) (w : (J₂.X q).V) :
    (c₃.comparison.f (0 + q)).hom (μ 0 q (c₁.ι.hom x) w) =
      P.resolutionCupPairing 0 q ((d X 0).hom x) ((c₂.comparison.f q).hom w) := by
  -- the action on a left product with `ι x` acts on `x` and on the right factor
  have hμι (p : ℕ) (g : G) (x : X.V) (w : (J₂.X p).V) :
      (J₃.X (0 + p)).ρ g (μ 0 p (c₁.ι.hom x) w) =
        μ 0 p (c₁.ι.hom (X.ρ g x)) ((J₂.X p).ρ g w) := by
    rw [← hρ, c₁.ι.hom.isIntertwining]
  -- the augmentation `d X 0` of the coinduced resolution includes `x` as a constant function
  have hdx (x : X.V) (g : G) : ((d X 0).hom x : C(G, X.V)) g = x := (rfl)
  have hgx (g : G) (x : X.V) : X.ρ g (X.ρ g⁻¹ x) = x :=
    Representation.self_inv_apply X.ρ.toRepresentation g x
  induction q generalizing x with
  | zero =>
    ext g
    refine (c₃.comparison_f_zero_apply_apply _ g).trans ?_
    rw [P.resolutionCupPairing_apply, P.resolutionCup_zero_apply]
    refine Eq.trans ?_ (P.pointwise_zero_apply rfl _ _).symm
    rw [hμι 0 g⁻¹ x w, hproj, ← P.equivariant, hgx, c₂.comparison_f_zero_apply_apply, hdx]
  | succ q ih =>
    refine ContinuousMap.ext fun g ↦ ?_
    refine (c₃.comparison_f_succ_apply_apply (0 + q) _ g).trans ?_
    -- the comparison recursion indexes the term as `J₃.X (0 + q + 1)`, which is
    -- `J₃.X (0 + (q + 1))` only up to definitional unfolding of the addition
    rw [show (J₃.X (0 + q + 1)).ρ g⁻¹ (μ 0 (q + 1) (c₁.ι.hom x) w) =
        μ 0 (q + 1) (c₁.ι.hom (X.ρ g⁻¹ x)) ((J₂.X (q + 1)).ρ g⁻¹ w) from hμι (q + 1) g⁻¹ x w,
      hhom, hμι q g, hgx, ih, ← c₂.comparison_f_succ_apply_apply, P.resolutionCupPairing_apply,
      P.resolutionCupPairing_apply, P.resolutionCup_zero_d_zero, P.resolutionCup_zero_apply, hdx]
    -- the target degrees `0 + q + 1` and `0 + (q + 1)` of the two pointwise pairings agree
    -- definitionally, and the degree proofs are irrelevant
    rfl

/-- The Alexander–Whitney product with a cocycle `β` on the right commutes with the differentials
of the coinduced resolutions, the target differential read into degree `r + 1 + q`. -/
private theorem resolution'_d_resolutionCupPairing {q : ℕ} (β : (resolution'X Y q).V)
    (hβ : (d Y (q + 1)).hom β = 0) (r : ℕ) (v : (resolution'X X r).V) :
    ((resolution' Z).d (r + q) (r + 1 + q)).hom (P.resolutionCupPairing r q v β) =
      P.resolutionCupPairing (r + 1) q (((resolution' X).d r (r + 1)).hom v) β := by
  -- the differential into degree `r + 1 + q` is the one into `r + q + 1`, transported
  have hdZ (j : ℕ) (h : r + q + 1 = j) (F : (resolution'X Z (r + q)).V) :
      ((resolution' Z).d (r + q) j).hom F =
        ((TopRep.resolution Z).XIsoOfEq (by omega : r + q + 1 + 1 = j + 1)).hom.hom
          ((d Z (r + q + 1)).hom F) := by
    subst h
    simp [ContIntertwiningMap.id_apply, resolution'd_eq]
  have hdX : ((resolution' X).d r (r + 1)).hom v = (d X (r + 1)).hom v := by
    simp only [resolution', CochainComplex.of_d, resolution'd_eq]
  rw [hdZ _ (by omega), hdX, P.resolutionCupPairing_apply, P.resolutionCupPairing_apply,
    P.resolutionCup_leibniz, hβ, ← zero_smul k (0 : (resolutionX Y (q + 1 + 1)).V),
    P.resolutionCup_smul_right, zero_smul, smul_zero, add_zero, P.resolutionCup_cast]

/-- **The class of a product is the cup product of the classes.** Let `μ` be an equivariant
pairing of complexes contracted onto `X`, `Y` and `Z`, lying over the coefficient pairing `P`,
continuous in its first argument, and satisfying the Leibniz rule `d (a · b) = d a · b` against
cocycles `b`. Suppose that multiplying on the left by an augmented element `ι x` commutes with the
contractions. Then for invariant cocycles `a` and `b`, the class of `a · b` is `[a] ⌣ [b]`. -/
theorem cohomologyClass_pairing [LocallyCompactSpace G]
    (hρ : ∀ p q g a b, μ p q ((J₁.X p).ρ g a) ((J₂.X q).ρ g b) = (J₃.X (p + q)).ρ g (μ p q a b))
    (hcont : ∀ p q b, Continuous fun a ↦ μ p q a b)
    (hd : ∀ p q a b, (J₂.d q (q + 1)).hom b = 0 →
      (J₃.d (p + q) (p + 1 + q)).hom (μ p q a b) = μ (p + 1) q ((J₁.d p (p + 1)).hom a) b)
    (hproj : ∀ x w, c₃.proj (μ 0 0 (c₁.ι.hom x) w) = P.bil x (c₂.proj w))
    (hhom : ∀ q x w,
      c₃.hom (0 + q) (μ 0 (q + 1) (c₁.ι.hom x) w) = μ 0 q (c₁.ι.hom x) (c₂.hom q w))
    {p q : ℕ} (a : (J₁.X p).ρ.invariants) (ha : (J₁.d p (p + 1)).hom (a : (J₁.X p).V) = 0)
    (b : (J₂.X q).ρ.invariants) (hb : (J₂.d q (q + 1)).hom (b : (J₂.X q).V) = 0) :
    c₃.cohomologyClass ⟨μ p q a b, fun g ↦ by rw [← hρ, a.2 g, b.2 g]⟩
        (by rw [show p + q + 1 = p + 1 + q by omega, hd p q a b hb, ha, LinearMap.map_zero₂]) =
      P.cup p q (c₁.cohomologyClass a ha) (c₂.cohomologyClass b hb) := by
  set β := (c₂.comparison.f q).hom.mapInvariants b
  -- multiplication by `b` on the right, and by `β` on the right
  let L (r : ℕ) : J₁.X r ⟶ J₃.X (r + q) := ofHom
    { (μ r q).flip b with
      cont := hcont r q b
      isIntertwining' g := ContinuousLinearMap.ext fun v ↦
        (congrArg (μ r q ((J₁.X r).ρ g v)) (b.2 g)).symm.trans (hρ r q g v b) }
  let R (r : ℕ) : (resolution' X).X r ⟶ (resolution' Z).X (r + q) := ofHom
    { (P.resolutionCupPairing r q).flip β.1 with
      cont := (P.continuous_resolutionCupPairing r q).comp (continuous_id.prodMk continuous_const)
      isIntertwining' g := ContinuousLinearMap.ext fun v ↦
        (congrArg (P.resolutionCupPairing r q (((resolution' X).X r).ρ g v)) (β.2 g)).symm.trans
          (P.resolutionCupPairing_ρ r q g v β.1) }
  have hα : ((homogeneousCochains X).d p (p + 1)).hom ((c₁.comparison.f p).hom.mapInvariants a) =
      0 := c₁.d_mapInvariants_comparison_f a ha
  have hβ : ((homogeneousCochains Y).d q (q + 1)).hom β = 0 := c₂.d_mapInvariants_comparison_f b hb
  have hβ' : (d Y (q + 1)).hom β.1 = 0 :=
    (homogeneousCochains.d_apply Y q β).symm.trans (congrArg Subtype.val hβ)
  have hRv (r : ℕ) (v : ((resolution' X).X r).V) :
      (R r).hom v = P.resolutionCupPairing r q v β.1 := (rfl)
  -- `μ (-, b)` and the right product with `β` commute with the differentials
  have hL (r : ℕ) : L r ≫ J₃.d (r + q) (r + 1 + q) = J₁.d r (r + 1) ≫ L (r + 1) :=
    ConcreteCategory.hom_ext _ _ fun v ↦ hd r q v b hb
  have hR (r : ℕ) :
      R r ≫ (resolution' Z).d (r + q) (r + 1 + q) = (resolution' X).d r (r + 1) ≫ R (r + 1) :=
    ConcreteCategory.hom_ext _ _ fun v ↦ by
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hRv, hRv]
      exact resolution'_d_resolutionCupPairing P β.1 hβ' r v
  -- on the augmentation both composites are the product of the constant cochain with `β`
  have h0 : c₁.ι ≫ L 0 ≫ c₃.comparison.f (0 + q) = c₁.ι ≫ c₁.comparison.f 0 ≫ R 0 :=
    ConcreteCategory.hom_ext _ _ fun x ↦ by
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← Category.assoc,
        ι_comp_comparison_f_zero, ConcreteCategory.comp_apply, hRv]
      exact comparison_f_pairing_ι c₁ c₂ c₃ P μ (hρ 0) hproj hhom q x b
  have hab' : ((homogeneousCochains Z).d (p + q) (p + q + 1)).hom
      (P.cupCochain p q ((c₁.comparison.f p).hom.mapInvariants a) β) = 0 := by
    rw [P.cupCochain_leibniz, hα, hβ, LinearMap.map_zero₂, map_zero, map_zero, smul_zero,
      add_zero]
  rw [cohomologyClass_def, cohomologyClass_def, cohomologyClass_def,
    P.cup_cochainClass p q _ hα _ hβ hab']
  convert c₁.cochainClass_eq_of_ι_comp_eq (n := q) (fun r ↦ L r ≫ c₃.comparison.f (r + q))
    (fun r ↦ c₁.comparison.f r ≫ R r)
    (fun r ↦ by rw [Category.assoc, c₃.comparison.comm, ← Category.assoc, hL, Category.assoc])
    (fun r ↦ by rw [Category.assoc, hR, ← Category.assoc, c₁.comparison.comm, Category.assoc])
    h0 a ha using 2
  · refine (Subtype.ext ?_).symm
    rw [ContIntertwiningMap.mapInvariants_apply, ContIntertwiningMap.mapInvariants_apply]
    exact ConcreteCategory.comp_apply _ _ _
  · refine (Subtype.ext ?_).symm
    rw [ContIntertwiningMap.mapInvariants_apply, P.coe_cupCochain, ← hRv]
    exact ConcreteCategory.comp_apply _ _ _

end Pairing

section GradedPairing

variable [CommRing k] [TopologicalSpace k] {X Y Z : TopRep.{max v w} k G}
  {M₁ M₂ M₃ : TopRep.{max v w} k G}
  {ℳ₁ : ℤ → Submodule k M₁.V} {hρ₁ : ∀ n g x, x ∈ ℳ₁ n → M₁.ρ g x ∈ ℳ₁ n} {d₁ : M₁ ⟶ M₁}
  {hd₁ : TauCeti.LinearMap.IsHomogeneous d₁.hom.toLinearMap ℳ₁ ℳ₁ 1} {hdd₁ : d₁ ≫ d₁ = 0}
  {ℳ₂ : ℤ → Submodule k M₂.V} {hρ₂ : ∀ n g x, x ∈ ℳ₂ n → M₂.ρ g x ∈ ℳ₂ n} {d₂ : M₂ ⟶ M₂}
  {hd₂ : TauCeti.LinearMap.IsHomogeneous d₂.hom.toLinearMap ℳ₂ ℳ₂ 1} {hdd₂ : d₂ ≫ d₂ = 0}
  {ℳ₃ : ℤ → Submodule k M₃.V} {hρ₃ : ∀ n g x, x ∈ ℳ₃ n → M₃.ρ g x ∈ ℳ₃ n} {d₃ : M₃ ⟶ M₃}
  {hd₃ : TauCeti.LinearMap.IsHomogeneous d₃.hom.toLinearMap ℳ₃ ℳ₃ 1} {hdd₃ : d₃ ≫ d₃ = 0}
  (c₁ : ResolutionContraction X (M₁.gradedCochainComplex ℳ₁ hρ₁ d₁ hd₁ hdd₁))
  (c₂ : ResolutionContraction Y (M₂.gradedCochainComplex ℳ₂ hρ₂ d₂ hd₂ hdd₂))
  (c₃ : ResolutionContraction Z (M₃.gradedCochainComplex ℳ₃ hρ₃ d₃ hd₃ hdd₃))
  (P : TauCeti.TopPairing X Y Z) (μ : M₁.V →ₗ[k] M₂.V →ₗ[k] M₃.V)

/-- **The class of a product of homogeneous cocycles is the cup product of their classes.** Let
`μ` be an equivariant bilinear pairing of graded representations whose complexes are contracted
onto `X`, `Y` and `Z`. Suppose that `μ` adds degrees, is continuous in its first argument, and
satisfies `d (a · b) = d a · b` whenever `d b = 0`, and that multiplying on the left by an
augmented element `ι x` commutes with the contractions, lying over the coefficient pairing `P`.
Then for homogeneous cocycles `a` and `b` fixed by `G`, the class of `a · b` is `[a] ⌣ [b]`. This
is `TopRep.ResolutionContraction.cohomologyClass_pairing` for products written on total
modules. -/
theorem gradedCohomologyClass_pairing [LocallyCompactSpace G]
    (hμ : ∀ {p q : ℤ} {a : M₁.V} {b : M₂.V}, a ∈ ℳ₁ p → b ∈ ℳ₂ q → μ a b ∈ ℳ₃ (p + q))
    (hρ : ∀ g a b, μ (M₁.ρ g a) (M₂.ρ g b) = M₃.ρ g (μ a b))
    (hcont : ∀ b, Continuous fun a ↦ μ a b)
    (hd : ∀ a b, d₂.hom b = 0 → d₃.hom (μ a b) = μ (d₁.hom a) b)
    (hproj : ∀ (x : X.V) (w : M₂.V) (hw : w ∈ ℳ₂ (0 : ℕ))
      (hxw : μ (c₁.ι.hom x).1 w ∈ ℳ₃ (0 : ℕ)),
      c₃.proj ⟨μ (c₁.ι.hom x).1 w, hxw⟩ = P.bil x (c₂.proj ⟨w, hw⟩))
    (hhom : ∀ (q : ℕ) (x : X.V) (w : M₂.V) (hw : w ∈ ℳ₂ (q + 1 : ℕ))
      (hxw : μ (c₁.ι.hom x).1 w ∈ ℳ₃ (q + 1 : ℕ)),
      (c₃.hom q ⟨μ (c₁.ι.hom x).1 w, hxw⟩).1 = μ (c₁.ι.hom x).1 (c₂.hom q ⟨w, hw⟩).1)
    {p q : ℕ} {a : M₁.V} (ha : a ∈ ℳ₁ p) (hainv : ∀ g, M₁.ρ g a = a) (hda : d₁.hom a = 0)
    {b : M₂.V} (hb : b ∈ ℳ₂ q) (hbinv : ∀ g, M₂.ρ g b = b) (hdb : d₂.hom b = 0) :
    c₃.gradedCohomologyClass (μ a b) (by exact_mod_cast hμ ha hb)
        (fun g ↦ by rw [← hρ, hainv, hbinv]) (by rw [hd a b hdb, hda, LinearMap.map_zero₂]) =
      P.cup p q (c₁.gradedCohomologyClass a ha hainv hda)
        (c₂.gradedCohomologyClass b hb hbinv hdb) := by
  have hμ' {p q : ℕ} {a : M₁.V} {b : M₂.V} (ha : a ∈ ℳ₁ p) (hb : b ∈ ℳ₂ q) :
      μ a b ∈ ℳ₃ (p + q : ℕ) := by
    exact_mod_cast hμ ha hb
  -- `μ` restricted to the terms of the complexes
  let μ' (p q : ℕ) : ((M₁.gradedCochainComplex ℳ₁ hρ₁ d₁ hd₁ hdd₁).X p).V →ₗ[k]
      ((M₂.gradedCochainComplex ℳ₂ hρ₂ d₂ hd₂ hdd₂).X q).V →ₗ[k]
        ((M₃.gradedCochainComplex ℳ₃ hρ₃ d₃ hd₃ hdd₃).X (p + q)).V :=
    LinearMap.mk₂ k (fun a b ↦ ⟨μ a.1 b.1, hμ' a.2 b.2⟩)
      (fun a a' b ↦ Subtype.ext (LinearMap.map_add₂ μ a.1 a'.1 b.1))
      (fun r a b ↦ Subtype.ext (LinearMap.map_smul₂ μ r a.1 b.1))
      (fun a b b' ↦ Subtype.ext (map_add (μ a.1) b.1 b'.1))
      (fun r a b ↦ Subtype.ext (map_smul (μ a.1) r b.1))
  have hμ'v (p q : ℕ) a b : (μ' p q a b).1 = μ a.1 b.1 := (rfl)
  -- the differential of `gradedCochainComplex` into any degree `j = i + 1` is `d`
  have hdv {M : TopRep.{max v w} k G} {ℳ : ℤ → Submodule k M.V}
      {hρ : ∀ n g x, x ∈ ℳ n → M.ρ g x ∈ ℳ n} {d : M ⟶ M}
      {hd : TauCeti.LinearMap.IsHomogeneous d.hom.toLinearMap ℳ ℳ 1} {hdd : d ≫ d = 0}
      (i j : ℕ) (hij : i + 1 = j) (v : ((M.gradedCochainComplex ℳ hρ d hd hdd).X i).V) :
      (((M.gradedCochainComplex ℳ hρ d hd hdd).d i j).hom v).1 = d.hom v.1 := by
    subst hij
    exact gradedCochainComplex_d_apply M ℳ hρ d hd hdd i v
  -- the contracting homotopy of `c₃` read in degree `i = q`
  have hhom' (q : ℕ) (x : X.V) (w : ((M₂.gradedCochainComplex ℳ₂ hρ₂ d₂ hd₂ hdd₂).X (q + 1)).V)
      (i : ℕ) (hi : i = q) (v : ((M₃.gradedCochainComplex ℳ₃ hρ₃ d₃ hd₃ hdd₃).X (i + 1)).V)
      (hv : v.1 = μ (c₁.ι.hom x).1 w.1) :
      (c₃.hom i v).1 = μ (c₁.ι.hom x).1 (c₂.hom q w).1 := by
    subst hi
    obtain ⟨v, hv'⟩ := v
    obtain rfl : v = μ (c₁.ι.hom x).1 w.1 := hv
    exact hhom i x w.1 w.2 hv'
  rw [gradedCohomologyClass_def, gradedCohomologyClass_def, gradedCohomologyClass_def]
  convert cohomologyClass_pairing c₁ c₂ c₃ P μ'
    (fun p q g a b ↦ Subtype.ext (by
      rw [hμ'v, gradedCochainComplex_ρ_apply, gradedCochainComplex_ρ_apply,
        gradedCochainComplex_ρ_apply, hρ, hμ'v]))
    (fun p q b ↦ (continuous_gradedCochainComplex_X_iff _ _ _ _ _ _ _ _).2
      ((hcont b.1).comp continuous_subtype_val))
    (fun p q a b hb ↦ Subtype.ext (by
      rw [hdv _ _ (by omega), hμ'v, hd a.1 b.1 ((hdv q (q + 1) rfl b).symm.trans
        (congrArg Subtype.val hb)), hμ'v, hdv p (p + 1) rfl a]))
    (fun x w ↦ hproj x w.1 w.2 _)
    (fun q x w ↦ Subtype.ext (hhom' q x w (0 + q) (Nat.zero_add q) _ (hμ'v _ _ _ _)))
    (gradedCochainComplexInvariant M₁ ℳ₁ hρ₁ d₁ hd₁ hdd₁ p a ha hainv)
    (gradedCochainComplex_d_invariant M₁ ℳ₁ hρ₁ d₁ hd₁ hdd₁ ha hainv hda)
    (gradedCochainComplexInvariant M₂ ℳ₂ hρ₂ d₂ hd₂ hdd₂ q b hb hbinv)
    (gradedCochainComplex_d_invariant M₂ ℳ₂ hρ₂ d₂ hd₂ hdd₂ hb hbinv hdb) using 2
  refine Subtype.ext (Subtype.ext ?_)
  rw [gradedCochainComplexInvariant_val, hμ'v, gradedCochainComplexInvariant_val,
    gradedCochainComplexInvariant_val]

end GradedPairing

end ResolutionContraction

end TopRep
