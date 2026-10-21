/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Commuting
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.FiniteType.Tensor.Product

/-!
# The semisimple-part endomorphism of a commutative affine group

Let `H` be the coordinate Hopf algebra of an affine group over a field `k`. A character of the
group, that is, a group-like element `c ∈ H`, cannot distinguish a point from its semisimple part:
`c(g_s) = c(g)`. Indeed `c` is a homomorphism to a diagonalizable group, Jordan decomposition is
natural, and every point of a diagonalizable group is semisimple.

Now let `k` be algebraically closed and let `H` be reduced, of finite type, and cocommutative, so
that `H` represents a reduced commutative affine group `G`. In each finite-dimensional
representation the semisimple parts of the points form a commuting family of semisimple operators.
Every joint eigenspace of this family is stable under all points, hence a subcomodule, hence
contains a weight vector; so each joint eigenvalue function is a character. Thus every matrix
coefficient of `g ↦ g_s` is a linear combination of characters, and in particular is a regular
function on `G`. Since `H` is reduced, its points separate its elements, and these regular
functions assemble into a bialgebra endomorphism `σ` of `H` with `g ∘ σ = g_s` for every point
`g`: the map `g ↦ g_s` is an endomorphism of the affine group `G`.

The endomorphism `σ` is idempotent and its image is the span of the group-like elements, the
coordinate ring of the diagonalizable quotient of `G`. On points it fixes exactly the semisimple
points and kills exactly the unipotent points. It is the input for realizing the semisimple and
unipotent points as closed subgroups `G_s` and `G_u` with `G ≅ G_s × G_u`.

Reducedness is what makes points determine the endomorphism: in characteristic `p`, the only point
of `αₚ` is the identity, so the identity and the trivial endomorphism of its coordinate ring both
induce `g ↦ g_s`.

## Main declarations

* `TauCeti.HopfAlgebra.Point.semisimplePart_apply_of_isGroupLikeElem`: characters take the same
  value on a point and on its semisimple part.
* `TauCeti.HopfAlgebra.Point.iSup_iInf_eigenspace_semisimplePart_eq_top`: in a finite-dimensional
  representation of a reduced commutative affine group, the semisimple parts of the points are
  simultaneously diagonalizable with characters as eigenvalues.
* `TauCeti.HopfAlgebra.Point.exists_mem_groupLikeSetSpan_forall_apply_eq`: every coordinate
  function evaluated at semisimple parts is a linear combination of characters.
* `TauCeti.HopfAlgebra.Point.semisimplePartBialgHom`: the semisimple-part endomorphism.
* `TauCeti.HopfAlgebra.Point.mapDomain_semisimplePartBialgHom` and
  `TauCeti.HopfAlgebra.Point.eq_semisimplePartBialgHom_iff`: its defining property on points and
  the resulting characterization.
* `TauCeti.HopfAlgebra.Point.range_semisimplePartBialgHom` and
  `TauCeti.HopfAlgebra.Point.semisimplePartBialgHom_comp_self`: it is an idempotent projection
  onto the span of the group-like elements.
* `TauCeti.HopfAlgebra.Point.mapDomain_semisimplePartBialgHom_eq_self_iff` and
  `TauCeti.HopfAlgebra.Point.mapDomain_semisimplePartBialgHom_eq_one_iff`: its fixed points are the
  semisimple points and its kernel consists of the unipotent points.

## References

* A. Borel, *Linear Algebraic Groups*, §4.7.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 3.1.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra.Point

universe u

section Character

variable (k H K : Type u) [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

/-- **Characters do not see unipotent parts.** A group-like element of the coordinate Hopf algebra
takes the same value on a point and on its semisimple part. -/
theorem semisimplePart_apply_of_isGroupLikeElem (g : WithConv (H →ₐ[k] K)) {c : H}
    (hc : IsGroupLikeElem k c) :
    (semisimplePart k H K g).ofConv c = g.ofConv c := by
  -- Precompose with the bialgebra map `k[GroupLike k H] → H`, whose source represents a
  -- diagonalizable group, all of whose points are their own semisimple parts.
  have h := semisimplePart_mapDomain (MonoidAlgebra.liftGroupLikeBialgHom (R := k) (A := H)) g
  rw [DiagonalizableGroup.semisimplePart_eq_self] at h
  have h' := congrArg (fun p ↦ p.ofConv
    (MonoidAlgebra.single (⟨c, hc⟩ : GroupLike k H) (1 : k) : MonoidAlgebra k (GroupLike k H))) h
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply] at h'
  simpa [MonoidAlgebra.liftGroupLikeBialgHom_single] using h'.symm

/-- The semisimple part of a base-valued point acts on a vector of group-like weight `c` by the
scalar `g c`. -/
theorem basePointsRepresentation_semisimplePart_of_mem_weightSpace
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [PerfectField k]
    (g : WithConv (H →ₐ[k] k)) {c : GroupLike k H} {v : M}
    (hv : v ∈ _root_.GroupLike.weightSpace (M := M) c) :
    Comodule.basePointsRepresentation (R := k) (H := H) M (semisimplePart k H k g) v =
      g.ofConv c • v := by
  rw [Comodule.basePointsRepresentation_apply_of_mem_weightSpace _ hv,
    semisimplePart_apply_of_isGroupLikeElem k H k g c.isGroupLikeElem_val]

end Character

section Commutative

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H]

/-- **Semisimple parts are simultaneously diagonalizable by characters.** In a finite-dimensional
representation of a reduced commutative affine group of finite type over an algebraically closed
field, the representation is spanned by the joint eigenspaces of the semisimple parts of the
points, and on each of them the semisimple part of `g` acts by `g c` for a character `c`. -/
theorem iSup_iInf_eigenspace_semisimplePart_eq_top
    (M : Type u) [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M] :
    ⨆ c : GroupLike k H, ⨅ g : WithConv (H →ₐ[k] k),
      (Comodule.basePointsRepresentation (R := k) (H := H) M
        (semisimplePart k H k g)).eigenspace (g.ofConv c) = ⊤ := by
  classical
  let ρ := Comodule.basePointsRepresentation (R := k) (H := H) M
  have hss : ∀ g, (ρ (semisimplePart k H k g)).IsSemisimple := fun g ↦
    IsSemisimplePoint.isSemisimple_basePointsRepresentation
      ((isSemisimplePoint_def _).mpr (isSemisimple_pointsAction_semisimplePart k H k g))
  rw [eq_top_iff, ← iSup_iInf_eigenspace_eq_top_of_isSemisimple
    (fun g ↦ ρ (semisimplePart k H k g)) (fun g h _ ↦ (Commute.all _ _).map ρ) hss]
  refine iSup_le fun χ ↦ ?_
  rcases eq_or_ne (⨅ g, (ρ (semisimplePart k H k g)).eigenspace (χ g)) ⊥ with hbot | hne
  · rw [hbot]
    exact bot_le
  set E := ⨅ g, (ρ (semisimplePart k H k g)).eigenspace (χ g)
  -- The joint eigenspace `E` is stable under every point, since the group is commutative.
  have hstable : ∀ h : WithConv (H →ₐ[k] k), ∀ x ∈ E, ρ h x ∈ E := by
    intro h x hx
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro g
    calc ρ (semisimplePart k H k g) (ρ h x) = ρ h (ρ (semisimplePart k H k g) x) :=
          LinearMap.congr_fun ((Commute.all _ h).map ρ).eq x
      _ = χ g • ρ h x := by rw [hx g, map_smul]
  -- A joint eigenvector of all points in `E` spans a point-stable line, hence is a weight vector.
  have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨μ, w, hw, hwmem⟩ := exists_jointEigenvector_of_pairwise_commute_of_isAlgClosed
    (fun h ↦ (ρ h).restrict (hstable h))
    (fun h h' _ ↦ LinearMap.restrict_commute ((Commute.all h h').map ρ) (hstable h) (hstable h'))
  have hw' : (w : M) ≠ 0 := by simpa using hw
  obtain ⟨c, hc⟩ :=
    (k ∙ (w : M)).exists_mem_groupLikeWeightSpace_of_basePointsRepresentation_stable
      (w : M) hw' rfl fun h m hm ↦ by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
        have hval := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp (hwmem h))
        rw [LinearMap.coe_restrict_apply] at hval
        rw [map_smul, hval]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  -- Comparing eigenvalues on the weight vector identifies `χ` with the character `c`.
  have hχ : ∀ g, χ g = g.ofConv c := by
    intro g
    have h1 : ρ (semisimplePart k H k g) w = χ g • (w : M) :=
      Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp w.2 g)
    have h2 : ρ (semisimplePart k H k g) w = g.ofConv c • (w : M) :=
      basePointsRepresentation_semisimplePart_of_mem_weightSpace k H g hc
    exact smul_left_injective k hw' (h1.symm.trans h2)
  refine le_trans ?_ (le_iSup _ c)
  simp only [E, hχ, ρ, le_refl]

/-- Every matrix coefficient of the semisimple parts of the points of a reduced commutative affine
group is a linear combination of characters. -/
private theorem exists_mem_groupLikeSetSpan_forall_apply_matrixCoefficient
    {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]
    (φ : Module.Dual k M) (v : M) :
    ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
      ∀ g : WithConv (H →ₐ[k] k),
        g.ofConv h = (semisimplePart k H k g).ofConv (Comodule.matrixCoefficient (C := H) φ v) := by
  have hv : v ∈ ⨆ c : GroupLike k H, ⨅ g : WithConv (H →ₐ[k] k),
      (Comodule.basePointsRepresentation (R := k) (H := H) M
        (semisimplePart k H k g)).eigenspace (g.ofConv c) := by
    rw [iSup_iInf_eigenspace_semisimplePart_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun x ↦
      ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ, ∀ g : WithConv (H →ₐ[k] k),
        g.ofConv h = (semisimplePart k H k g).ofConv (Comodule.matrixCoefficient (C := H) φ x))
    hv (fun c x hx ↦ ?_) ⟨0, zero_mem _, fun g ↦ by simp⟩ fun x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩ ↦
      ⟨a + b, add_mem ha hb, fun g ↦ by simp [hxa, hyb]⟩
  refine ⟨φ x • (c : H), Submodule.smul_mem _ _
    (Subcoalgebra.groupLike_mem_groupLikeSetSpan (Set.mem_univ c)), fun g ↦ ?_⟩
  rw [Comodule.apply_matrixCoefficient,
    Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx g)]
  simp [mul_comm]

/-- **The semisimple part is a regular function of the point.** For a reduced commutative affine
group of finite type over an algebraically closed field, every coordinate function evaluated on
semisimple parts, `g ↦ f(g_s)`, is given by an element of the span of the characters. -/
theorem exists_mem_groupLikeSetSpan_forall_apply_eq (f : H) :
    ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
      ∀ g : WithConv (H →ₐ[k] k), g.ofConv h = (semisimplePart k H k g).ofConv f := by
  obtain ⟨N, hNfin, hf⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) (M := H) f
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have _ : Module.Finite k N := hNfin
  simpa only [Comodule.matrixCoefficient_counit_comp_subtype] using
    exists_mem_groupLikeSetSpan_forall_apply_matrixCoefficient (H := H)
      ((Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype N)) ⟨f, hf⟩

omit [Coalgebra.IsCocomm k H] in
/-- Points valued in the algebraically closed base field separate elements of `H`. -/
private theorem eq_of_forall_point_apply_eq {x y : H}
    (h : ∀ g : WithConv (H →ₐ[k] k), g.ofConv x = g.ofConv y) : x = y :=
  eq_of_forall_algHom_apply_eq (K := k) fun f ↦ h (toConv f)

variable (k) in
/-- The underlying function of the semisimple-part endomorphism, chosen pointwise. -/
private noncomputable def semisimplePartFun (f : H) : H :=
  (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) f).choose

private theorem apply_semisimplePartFun (g : WithConv (H →ₐ[k] k)) (f : H) :
    g.ofConv (semisimplePartFun k f) = (semisimplePart k H k g).ofConv f :=
  (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) f).choose_spec.2 g

variable (k H) in
/-- The algebra endomorphism underlying the semisimple-part endomorphism. -/
private noncomputable def semisimplePartAlgHom : H →ₐ[k] H where
  toFun := semisimplePartFun k
  map_one' := eq_of_forall_point_apply_eq fun g ↦ by
    rw [apply_semisimplePartFun, map_one, map_one]
  map_mul' x y := eq_of_forall_point_apply_eq fun g ↦ by
    rw [apply_semisimplePartFun, map_mul, map_mul, apply_semisimplePartFun,
      apply_semisimplePartFun]
  map_zero' := eq_of_forall_point_apply_eq fun g ↦ by
    rw [apply_semisimplePartFun, map_zero, map_zero]
  map_add' x y := eq_of_forall_point_apply_eq fun g ↦ by
    rw [apply_semisimplePartFun, map_add, map_add, apply_semisimplePartFun,
      apply_semisimplePartFun]
  commutes' r := eq_of_forall_point_apply_eq fun g ↦ by
    rw [apply_semisimplePartFun, AlgHom.commutes, AlgHom.commutes]

private theorem semisimplePartAlgHom_apply (f : H) :
    semisimplePartAlgHom k H f = semisimplePartFun k f :=
  rfl

private theorem toConv_comp_semisimplePartAlgHom (g : WithConv (H →ₐ[k] k)) :
    toConv (g.ofConv.comp (semisimplePartAlgHom k H)) = semisimplePart k H k g := by
  apply WithConv.ofConv_injective
  ext f
  rw [ofConv_toConv, AlgHom.comp_apply, semisimplePartAlgHom_apply, apply_semisimplePartFun]

variable (k H) in
/-- **The semisimple-part endomorphism of a commutative affine group.** For a reduced commutative
affine group of finite type over an algebraically closed field, this is the bialgebra
endomorphism of the coordinate Hopf algebra representing the group endomorphism `g ↦ g_s`; see
`mapDomain_semisimplePartBialgHom`. -/
noncomputable def semisimplePartBialgHom : H →ₐc[k] H :=
  BialgHom.ofAlgHom (semisimplePartAlgHom k H)
    (by
      -- The counit is evaluation at the identity point, which is its own semisimple part.
      ext f
      have h := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f)
        (toConv_comp_semisimplePartAlgHom (k := k) (H := H) 1)
      simpa [semisimplePart_one] using h)
    (by
      -- Points of `H ⊗ H` are pairs of points, and on a pair the comultiplication is the
      -- convolution product; the semisimple part of a product of commuting points is the product
      -- of the semisimple parts.
      ext f
      let _ : Algebra.FiniteType k (H ⊗[k] H) :=
        FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) H H
      refine eq_of_forall_algHom_apply_eq (k := k) (A := H ⊗[k] H) (K := k) fun φ ↦ ?_
      let g : WithConv (H →ₐ[k] k) := toConv (φ.comp Algebra.TensorProduct.includeLeft)
      let h : WithConv (H →ₐ[k] k) := toConv (φ.comp Algebra.TensorProduct.includeRight)
      have hφ : φ = Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ .all _ _) :=
        Algebra.TensorProduct.ext (by ext; simp [g]) (by ext; simp [h])
      have hσ : φ.comp (Algebra.TensorProduct.map (semisimplePartAlgHom k H)
          (semisimplePartAlgHom k H)) =
          Algebra.TensorProduct.lift (g.ofConv.comp (semisimplePartAlgHom k H))
            (h.ofConv.comp (semisimplePartAlgHom k H)) (fun _ _ ↦ .all _ _) :=
        Algebra.TensorProduct.ext (by ext; simp [g]) (by ext; simp [h])
      -- Evaluate both sides at `φ = (g, h)`: each is the value of `(g * h)_s = g_s * h_s` at `f`.
      have hl : φ (Algebra.TensorProduct.map (semisimplePartAlgHom k H)
          (semisimplePartAlgHom k H) (Coalgebra.comul (R := k) f)) =
          (semisimplePart k H k (g * h)).ofConv f := by
        rw [semisimplePart_mul_of_commute k H k (Commute.all g h),
          ← toConv_comp_semisimplePartAlgHom, ← toConv_comp_semisimplePartAlgHom,
          AlgHom.convMul_apply, ← hσ, AlgHom.comp_apply]
      have hr : φ (Coalgebra.comul (R := k) (semisimplePartAlgHom k H f)) =
          (semisimplePart k H k (g * h)).ofConv f := by
        rw [semisimplePartAlgHom_apply, ← apply_semisimplePartFun, AlgHom.convMul_apply, ← hφ]
      simpa [Bialgebra.comulAlgHom_apply] using hl.trans hr.symm)

/-- **The semisimple-part endomorphism represents `g ↦ g_s`.** -/
@[simp]
theorem apply_semisimplePartBialgHom (g : WithConv (H →ₐ[k] k)) (f : H) :
    g.ofConv (semisimplePartBialgHom k H f) = (semisimplePart k H k g).ofConv f :=
  apply_semisimplePartFun g f

/-- Precomposition with the semisimple-part endomorphism sends every point to its semisimple
part. -/
theorem mapDomain_semisimplePartBialgHom (g : WithConv (H →ₐ[k] k)) :
    BialgHom.mapDomain (semisimplePartBialgHom k H) g = semisimplePart k H k g := by
  apply WithConv.ofConv_injective
  ext f
  rw [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    apply_semisimplePartBialgHom]

/-- Simp-normal form of `mapDomain_semisimplePartBialgHom`, written after normalization by
`BialgHom.mapDomain_apply`. -/
@[simp]
theorem toConv_comp_semisimplePartBialgHom (g : WithConv (H →ₐ[k] k)) :
    toConv (g.ofConv.comp (semisimplePartBialgHom k H : H →ₐ[k] H)) = semisimplePart k H k g := by
  simpa only [BialgHom.mapDomain_apply] using mapDomain_semisimplePartBialgHom g

/-- The semisimple-part endomorphism is the unique bialgebra endomorphism representing
`g ↦ g_s`. -/
theorem eq_semisimplePartBialgHom_iff (φ : H →ₐc[k] H) :
    φ = semisimplePartBialgHom k H ↔
      ∀ g : WithConv (H →ₐ[k] k), BialgHom.mapDomain φ g = semisimplePart k H k g := by
  refine ⟨fun h g ↦ h ▸ mapDomain_semisimplePartBialgHom g, fun h ↦ ?_⟩
  ext f
  refine eq_of_forall_point_apply_eq (k := k) fun g ↦ ?_
  have hg := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv f) (h g)
  simpa [BialgHom.mapDomain_apply] using hg

/-- The semisimple-part endomorphism takes values in the span of the characters. -/
theorem semisimplePartBialgHom_mem_groupLikeSetSpan (f : H) :
    semisimplePartBialgHom k H f ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ :=
  (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) f).choose_spec.1

/-- The semisimple-part endomorphism fixes every character. -/
theorem semisimplePartBialgHom_apply_of_isGroupLikeElem {c : H} (hc : IsGroupLikeElem k c) :
    semisimplePartBialgHom k H c = c :=
  eq_of_forall_point_apply_eq fun g ↦ by
    rw [apply_semisimplePartBialgHom, semisimplePart_apply_of_isGroupLikeElem k H k g hc]

/-- The semisimple-part endomorphism fixes the span of the characters. -/
theorem semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan {f : H}
    (hf : f ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ) :
    semisimplePartBialgHom k H f = f := by
  rw [Subcoalgebra.mem_groupLikeSetSpan] at hf
  refine LinearMap.eqOn_span (f := (semisimplePartBialgHom k H : H →ₗ[k] H)) (g := LinearMap.id)
    ?_ hf
  rintro _ ⟨c, -, rfl⟩
  exact semisimplePartBialgHom_apply_of_isGroupLikeElem (k := k) c.isGroupLikeElem_val

/-- **The semisimple-part endomorphism projects onto the characters.** Its range is the span of
the group-like elements, the coordinate ring of the diagonalizable quotient. -/
theorem range_semisimplePartBialgHom :
    LinearMap.range (semisimplePartBialgHom k H : H →ₗ[k] H) =
      (Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ).toSubmodule := by
  refine le_antisymm ?_ fun f hf ↦ ⟨f, semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan hf⟩
  rintro _ ⟨f, rfl⟩
  exact semisimplePartBialgHom_mem_groupLikeSetSpan f

/-- **The semisimple-part endomorphism is idempotent.** -/
@[simp]
theorem semisimplePartBialgHom_comp_self :
    (semisimplePartBialgHom k H).comp (semisimplePartBialgHom k H) =
      semisimplePartBialgHom k H := by
  ext f
  exact semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan
    (semisimplePartBialgHom_mem_groupLikeSetSpan f)

/-- The points fixed by the semisimple-part endomorphism are exactly the semisimple points. -/
theorem mapDomain_semisimplePartBialgHom_eq_self_iff (g : WithConv (H →ₐ[k] k)) :
    BialgHom.mapDomain (semisimplePartBialgHom k H) g = g ↔ IsSemisimplePoint g := by
  rw [mapDomain_semisimplePartBialgHom]
  refine ⟨fun h ↦ h ▸ (isSemisimplePoint_def _).mpr
    (isSemisimple_pointsAction_semisimplePart k H k g), fun h ↦ ?_⟩
  exact semisimplePart_eq_self k H k ((isSemisimplePoint_def g).mp h)

/-- The kernel of the semisimple-part endomorphism on points consists exactly of the unipotent
points. -/
theorem mapDomain_semisimplePartBialgHom_eq_one_iff (g : WithConv (H →ₐ[k] k)) :
    BialgHom.mapDomain (semisimplePartBialgHom k H) g = 1 ↔ IsUnipotentPoint g := by
  rw [mapDomain_semisimplePartBialgHom, isUnipotentPoint_iff_semisimplePart_eq_one]

end Commutative

end TauCeti.HopfAlgebra.Point
