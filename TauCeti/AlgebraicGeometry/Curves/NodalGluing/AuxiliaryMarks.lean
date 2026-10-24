/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Iso
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Logic.Equiv.Sum

/-!
# Marked nodal curves with unordered auxiliary marks

A marked nodal curve carries marks (`NodalGluing.Marking`), labelled by an arbitrary type:
pairwise distinct points of its normalization, none of them a flag point.  Some of the marks are
*distinguished* and keep their ordering, labelled by a type `N`; the others are *auxiliary*,
labelled by a type `R`, and only the set of them matters.  An isomorphism of such curves is an
isomorphism of nodal curves `f` together with a permutation `π` of the auxiliary labels, such that
`f` fixes every distinguished label and carries the auxiliary mark `j` to the auxiliary mark
`π j`.  These arrows form a groupoid, the label-permutation extension of the groupoid of
isomorphisms preserving every label (a finite extension when `R` is finite): the ordered
isomorphisms are exactly the arrows with `π = 1`.

Because the auxiliary marks are pairwise distinct, the permutation is determined by the map of
curves (`AuxiliaryIso.toIso_injective`), so the arrows carry no data beyond the map.  The arrows
with a fixed permutation form a torsor for the group of ordered automorphisms of the source
(`AuxiliaryIso.permFiberEquiv`).  Hence when that group is finite and there are finitely many
auxiliary labels, every set of arrows is finite (`AuxiliaryIso.finite`).  The finiteness of the
ordered automorphism group is a hypothesis here: for stable marked curves it is a theorem of the
analytic theory, which this file does not prove.

## Main definitions

The marks `NodalGluing.Marking d L` on the nodal curve presented by `d`, labelled by `L`, are
defined in `TauCeti.AlgebraicGeometry.Curves.NodalGluing.Basic`.

* `NodalGluing.AuxiliaryIso I n m m'`: the arrows `(π, f)` between curves with marks
  `m : Marking d (N ⊕ R)` and `m' : Marking d' (N ⊕ R)`, with identity `AuxiliaryIso.refl`,
  composite `AuxiliaryIso.trans` (`(ρ, h) ∘ (π, f) = (ρ ∘ π, h ∘ f)`) and inverse
  `AuxiliaryIso.symm`.
* `NodalGluing.AuxiliaryAut I n m`: the automorphism group of a curve with unordered auxiliary
  marks, with its permutation action on the auxiliary labels (`AuxiliaryAut.auxiliaryPerm`), its
  forgetful map to the automorphisms of the nodal curve (`AuxiliaryAut.toAut`) and the subgroup
  of ordered automorphisms (`AuxiliaryAut.ordered`).
* `NodalGluing.AuxiliaryMarkedCurve I n N R`: the bundled curves with `N` distinguished and `R`
  auxiliary marks, with the groupoid structure `unorderedAuxiliaryIsomorphismGroupoid` given by
  the arrows `(π, f)`.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for marked nodal Riemann surfaces and their isomorphisms
  (Definition 3.2) and for the finiteness of the automorphism group of a stable marked curve.
* Enrico Arbarello, Maurizio Cornalba, Phillip A. Griffiths, *Geometry of Algebraic Curves,
  Volume II*, Chapter X, for pointed nodal curves and their isomorphisms.
-/

public noncomputable section

open Set CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

universe u v w

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {ι' Flag' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace H (X' i)]
  {ι'' Flag'' : Type*} {X'' : ι'' → Type*} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ChartedSpace H (X'' i)]
  {d : FlagPairData ι Flag X} {d' : FlagPairData ι' Flag' X'} {d'' : FlagPairData ι'' Flag'' X''}

/-! ### Arrows with unordered auxiliary marks -/

variable {N R : Type*}

variable (I n) in
/-- **An isomorphism of curves with unordered auxiliary marks.**  The marks are labelled by
`N ⊕ R`: the labels in `N` are distinguished and ordered, those in `R` are auxiliary.  An arrow
is a pair `(π, f)` of a permutation `π` of the auxiliary labels and an isomorphism `f` of nodal
curves which fixes every distinguished label and carries the auxiliary mark `j` to the auxiliary
mark `π j`. -/
structure AuxiliaryIso (m : Marking d (N ⊕ R)) (m' : Marking d' (N ⊕ R)) where
  /-- The isomorphism of nodal curves. -/
  toIso : Iso I n d d'
  /-- The permutation of the auxiliary labels. -/
  perm : Equiv.Perm R
  /-- The isomorphism fixes every distinguished label. -/
  apply_inl' (a : N) : toIso (m.point (.inl a)) = m'.point (.inl a)
  /-- The isomorphism carries the auxiliary mark `j` to the auxiliary mark `perm j`. -/
  apply_inr' (j : R) : toIso (m.point (.inr j)) = m'.point (.inr (perm j))

namespace AuxiliaryIso

variable {m : Marking d (N ⊕ R)} {m' : Marking d' (N ⊕ R)} {m'' : Marking d'' (N ⊕ R)}

instance : EquivLike (AuxiliaryIso I n m m') (Σ i, X i) (Σ i, X' i) where
  coe e := e.toIso
  inv e := e.toIso.symm
  left_inv e := e.toIso.symm_apply_apply
  right_inv e := e.toIso.apply_symm_apply
  coe_injective' e e' h _ := by
    obtain ⟨f, π, hf, hπ⟩ := e
    obtain ⟨f', π', hf', hπ'⟩ := e'
    obtain rfl : f = f' := Iso.ext (congrFun h)
    obtain rfl : π = π' := Equiv.ext fun j ↦ Sum.inr_injective <| m'.point_injective <| by
      rw [← hπ, ← hπ']
    rfl

/-- The underlying isomorphism of nodal curves acts as the arrow. -/
@[simp] theorem coe_toIso (e : AuxiliaryIso I n m m') : ⇑e.toIso = e :=
  (rfl)

/-- An arrow fixes every distinguished label. -/
@[simp] theorem apply_inl (e : AuxiliaryIso I n m m') (a : N) :
    e (m.point (.inl a)) = m'.point (.inl a) :=
  e.apply_inl' a

/-- An arrow carries the auxiliary mark `j` to the auxiliary mark `e.perm j`. -/
@[simp] theorem apply_inr (e : AuxiliaryIso I n m m') (j : R) :
    e (m.point (.inr j)) = m'.point (.inr (e.perm j)) :=
  e.apply_inr' j

/-- **The permutation is determined by the map.**  The permutation of an arrow sends `j` to `k`
exactly when the arrow carries the auxiliary mark `j` to the auxiliary mark `k`. -/
theorem perm_apply_eq_iff (e : AuxiliaryIso I n m m') (j k : R) :
    e.perm j = k ↔ e (m.point (.inr j)) = m'.point (.inr k) := by
  rw [apply_inr, m'.point_injective.eq_iff, Sum.inr.injEq]

/-- Two arrows agreeing at every point of the normalization are equal. -/
@[ext] theorem ext {e e' : AuxiliaryIso I n m m'} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/-- An arrow is determined by its isomorphism of nodal curves: the permutation of the auxiliary
labels is recovered from the map, because the auxiliary marks are pairwise distinct. -/
theorem toIso_injective :
    Function.Injective (toIso : AuxiliaryIso I n m m' → Iso I n d d') :=
  fun _ _ h ↦ ext fun x ↦ congrArg (· x) h

/-- An arrow maps marks exactly to marks of the same kind. -/
theorem apply_point (e : AuxiliaryIso I n m m') (l : N ⊕ R) :
    e (m.point l) = m'.point (Sum.map id e.perm l) := by
  cases l <;> simp

variable (I n m) in
/-- The identity arrow, with the identity permutation. -/
protected def refl : AuxiliaryIso I n m m where
  toIso := Iso.refl I n d
  perm := Equiv.refl R
  apply_inl' _ := Iso.refl_apply _
  apply_inr' _ := Iso.refl_apply _

/-- The identity arrow fixes every point. -/
@[simp] theorem refl_apply (x : Σ i, X i) : AuxiliaryIso.refl I n m x = x :=
  Iso.refl_apply x

/-- The identity arrow is the identity isomorphism of nodal curves. -/
@[simp] theorem toIso_refl : (AuxiliaryIso.refl I n m).toIso = Iso.refl I n d :=
  (rfl)

/-- The identity arrow has the identity permutation. -/
@[simp] theorem perm_refl : (AuxiliaryIso.refl I n m).perm = Equiv.refl R :=
  (rfl)

/-- The inverse arrow `(π⁻¹, f⁻¹)`. -/
protected def symm (e : AuxiliaryIso I n m m') : AuxiliaryIso I n m' m where
  toIso := e.toIso.symm
  perm := e.perm.symm
  apply_inl' a := by rw [Iso.symm_apply_eq, coe_toIso, apply_inl]
  apply_inr' j := by rw [Iso.symm_apply_eq, coe_toIso, apply_inr, Equiv.apply_symm_apply]

/-- The inverse arrow undoes the arrow. -/
@[simp] theorem symm_apply_apply (e : AuxiliaryIso I n m m') (x : Σ i, X i) :
    e.symm (e x) = x :=
  e.toIso.symm_apply_apply x

/-- The arrow undoes its inverse. -/
@[simp] theorem apply_symm_apply (e : AuxiliaryIso I n m m') (y : Σ i, X' i) :
    e (e.symm y) = y :=
  e.toIso.apply_symm_apply y

/-- The isomorphism of nodal curves underlying the inverse arrow is the inverse isomorphism. -/
@[simp] theorem toIso_symm (e : AuxiliaryIso I n m m') : e.symm.toIso = e.toIso.symm :=
  (rfl)

/-- The permutation of the inverse arrow is the inverse permutation. -/
@[simp] theorem perm_symm (e : AuxiliaryIso I n m m') : e.symm.perm = e.perm.symm :=
  (rfl)

/-- The inverse of the inverse is the original arrow. -/
@[simp] theorem symm_symm (e : AuxiliaryIso I n m m') : e.symm.symm = e :=
  toIso_injective e.toIso.symm_symm

/-- The inverse of the identity arrow is the identity. -/
@[simp] theorem symm_refl : (AuxiliaryIso.refl I n m).symm = AuxiliaryIso.refl I n m :=
  toIso_injective Iso.symm_refl

/-- The composite `(ρ, h) ∘ (π, f) = (ρ ∘ π, h ∘ f)` of two arrows. -/
protected def trans (e : AuxiliaryIso I n m m') (e' : AuxiliaryIso I n m' m'') :
    AuxiliaryIso I n m m'' where
  toIso := e.toIso.trans e'.toIso
  perm := e.perm.trans e'.perm
  apply_inl' a := by rw [Iso.trans_apply, coe_toIso, coe_toIso, apply_inl, apply_inl]
  apply_inr' j := by
    rw [Iso.trans_apply, coe_toIso, coe_toIso, apply_inr, apply_inr, Equiv.trans_apply]

/-- The composite acts by applying the first arrow, then the second. -/
@[simp] theorem trans_apply (e : AuxiliaryIso I n m m') (e' : AuxiliaryIso I n m' m'')
    (x : Σ i, X i) : e.trans e' x = e' (e x) :=
  Iso.trans_apply _ _ x

/-- The isomorphism of nodal curves underlying a composite is the composite isomorphism. -/
@[simp] theorem toIso_trans (e : AuxiliaryIso I n m m') (e' : AuxiliaryIso I n m' m'') :
    (e.trans e').toIso = e.toIso.trans e'.toIso :=
  (rfl)

/-- The permutation of a composite is the composite of the permutations. -/
@[simp] theorem perm_trans (e : AuxiliaryIso I n m m') (e' : AuxiliaryIso I n m' m'') :
    (e.trans e').perm = e.perm.trans e'.perm :=
  (rfl)

/-- The inverse of a composite is the composite of the inverses in the opposite order. -/
@[simp] theorem symm_trans (e : AuxiliaryIso I n m m') (e' : AuxiliaryIso I n m' m'') :
    (e.trans e').symm = e'.symm.trans e.symm :=
  toIso_injective (Iso.symm_trans _ _)

/-- An arrow followed by its inverse is the identity. -/
@[simp] theorem self_trans_symm (e : AuxiliaryIso I n m m') :
    e.trans e.symm = AuxiliaryIso.refl I n m :=
  toIso_injective e.toIso.self_trans_symm

/-- The inverse of an arrow followed by it is the identity. -/
@[simp] theorem symm_trans_self (e : AuxiliaryIso I n m m') :
    e.symm.trans e = AuxiliaryIso.refl I n m' :=
  toIso_injective e.toIso.symm_trans_self

/-- Composing with the identity on the right does nothing. -/
@[simp] theorem trans_refl (e : AuxiliaryIso I n m m') : e.trans (AuxiliaryIso.refl I n m') = e :=
  toIso_injective e.toIso.trans_refl

/-- Composing with the identity on the left does nothing. -/
@[simp] theorem refl_trans (e : AuxiliaryIso I n m m') : (AuxiliaryIso.refl I n m).trans e = e :=
  toIso_injective e.toIso.refl_trans

/-- Composition of arrows is associative. -/
theorem trans_assoc {ι₃ Flag₃ : Type*} {X₃ : ι₃ → Type*} [∀ i, TopologicalSpace (X₃ i)]
    [∀ i, ChartedSpace H (X₃ i)] {d₃ : FlagPairData ι₃ Flag₃ X₃} {m₃ : Marking d₃ (N ⊕ R)}
    (e : AuxiliaryIso I n m m') (e' : AuxiliaryIso I n m' m'') (e'' : AuxiliaryIso I n m'' m₃) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  toIso_injective (Iso.trans_assoc _ _ _)

end AuxiliaryIso

/-! ### The automorphism group -/

variable (I n) in
/-- **The automorphism group of a curve with unordered auxiliary marks**: its arrows `(π, f)` to
itself, with composition as multiplication.  These are the isomorphisms of the nodal curve fixing
the distinguished labels and permuting the auxiliary marks, each with the permutation it
induces. -/
abbrev AuxiliaryAut (m : Marking d (N ⊕ R)) : Type _ := AuxiliaryIso I n m m

namespace AuxiliaryAut

variable {m : Marking d (N ⊕ R)}

instance : One (AuxiliaryAut I n m) := ⟨AuxiliaryIso.refl I n m⟩

instance : Mul (AuxiliaryAut I n m) := ⟨fun e e' ↦ e'.trans e⟩

instance : Inv (AuxiliaryAut I n m) := ⟨AuxiliaryIso.symm⟩

instance : Group (AuxiliaryAut I n m) where
  mul_assoc e e' e'' := (AuxiliaryIso.trans_assoc e'' e' e).symm
  one_mul := AuxiliaryIso.trans_refl
  mul_one := AuxiliaryIso.refl_trans
  inv_mul_cancel := AuxiliaryIso.self_trans_symm

/-- Multiplication of automorphisms is composition, the right factor acting first. -/
theorem mul_def (e e' : AuxiliaryAut I n m) : e * e' = e'.trans e :=
  (rfl)

/-- The unit automorphism is the identity arrow. -/
theorem one_def : (1 : AuxiliaryAut I n m) = AuxiliaryIso.refl I n m :=
  (rfl)

/-- The inverse automorphism is the inverse arrow. -/
theorem inv_def (e : AuxiliaryAut I n m) : e⁻¹ = e.symm :=
  (rfl)

/-- A product of automorphisms acts by composition. -/
@[simp] theorem mul_apply (e e' : AuxiliaryAut I n m) (x : Σ i, X i) : (e * e') x = e (e' x) :=
  AuxiliaryIso.trans_apply e' e x

/-- The unit automorphism fixes every point. -/
@[simp] theorem one_apply (x : Σ i, X i) : (1 : AuxiliaryAut I n m) x = x :=
  AuxiliaryIso.refl_apply x

/-- The inverse automorphism acts as the inverse arrow. -/
@[simp] theorem inv_apply (e : AuxiliaryAut I n m) (x : Σ i, X i) : e⁻¹ x = e.symm x :=
  (rfl)

/-- **The permutation action** of the automorphism group on the auxiliary labels. -/
def auxiliaryPerm : AuxiliaryAut I n m →* Equiv.Perm R where
  toFun e := e.perm
  map_one' := AuxiliaryIso.perm_refl
  map_mul' e e' := AuxiliaryIso.perm_trans e' e

/-- The permutation action of an automorphism is its permutation. -/
@[simp] theorem auxiliaryPerm_apply (e : AuxiliaryAut I n m) : auxiliaryPerm e = e.perm :=
  (rfl)

/-- The automorphism of the nodal curve underlying an automorphism with auxiliary marks. -/
def toAut : AuxiliaryAut I n m →* Aut I n d where
  toFun e := e.toIso
  map_one' := AuxiliaryIso.toIso_refl
  map_mul' e e' := AuxiliaryIso.toIso_trans e' e

/-- The underlying automorphism of the nodal curve is the underlying isomorphism. -/
@[simp] theorem toAut_apply (e : AuxiliaryAut I n m) : toAut e = e.toIso :=
  (rfl)

/-- The automorphism group with auxiliary marks is a subgroup of the automorphism group of the
nodal curve: an automorphism is determined by its map of curves. -/
theorem toAut_injective : Function.Injective (toAut : AuxiliaryAut I n m →* Aut I n d) :=
  AuxiliaryIso.toIso_injective

variable (I n m) in
/-- **The ordered automorphisms**: the automorphisms fixing every label, distinguished or
auxiliary.  They are the kernel of the permutation action on the auxiliary labels. -/
def ordered : Subgroup (AuxiliaryAut I n m) :=
  auxiliaryPerm.ker

/-- An automorphism is ordered exactly when its permutation of the auxiliary labels is
trivial. -/
@[simp] theorem mem_ordered_iff (e : AuxiliaryAut I n m) : e ∈ ordered I n m ↔ e.perm = 1 :=
  MonoidHom.mem_ker

/-- An automorphism is ordered exactly when it fixes every mark. -/
theorem mem_ordered_iff_forall (e : AuxiliaryAut I n m) :
    e ∈ ordered I n m ↔ ∀ l, e (m.point l) = m.point l := by
  rw [mem_ordered_iff]
  constructor
  · rintro h (a | j)
    · exact e.apply_inl a
    · rw [e.apply_inr, h, Equiv.Perm.one_apply]
  · intro h
    exact Equiv.ext fun j ↦ (e.perm_apply_eq_iff j j).mpr (h (.inr j))

end AuxiliaryAut

/-! ### Arrows with a fixed permutation, and finiteness -/

namespace AuxiliaryIso

variable {m : Marking d (N ⊕ R)} {m' : Marking d' (N ⊕ R)}

/-- **The arrows with a fixed permutation form a torsor for the ordered automorphisms.**  Given
one arrow `e₀`, an arrow `e` with the same permutation differs from `e₀` by the ordered
automorphism `e₀⁻¹ ∘ e` of the source, and every ordered automorphism `g` of the source gives the
arrow `e₀ ∘ g` with the permutation of `e₀`. -/
def permFiberEquiv (e₀ : AuxiliaryIso I n m m') :
    {e : AuxiliaryIso I n m m' // e.perm = e₀.perm} ≃ AuxiliaryAut.ordered I n m where
  toFun e := ⟨e.1.trans e₀.symm, by
    rw [AuxiliaryAut.mem_ordered_iff, perm_trans, perm_symm, e.2, Equiv.self_trans_symm,
      Equiv.Perm.one_def]⟩
  invFun g := ⟨g.1.trans e₀, by
    have hg := (AuxiliaryAut.mem_ordered_iff g.1).mp g.2
    rw [perm_trans, hg, Equiv.Perm.one_def, Equiv.refl_trans]⟩
  left_inv e := Subtype.ext <| ext fun x ↦ by simp
  right_inv g := Subtype.ext <| ext fun x ↦ by simp

/-- The ordered automorphism attached to an arrow `e` with the permutation of `e₀` is
`e₀⁻¹ ∘ e`. -/
@[simp] theorem coe_permFiberEquiv_apply (e₀ : AuxiliaryIso I n m m')
    (e : {e : AuxiliaryIso I n m m' // e.perm = e₀.perm}) :
    (e₀.permFiberEquiv e : AuxiliaryAut I n m) = e.1.trans e₀.symm :=
  (rfl)

/-- The arrow attached to an ordered automorphism `g` is `e₀ ∘ g`. -/
@[simp] theorem coe_permFiberEquiv_symm_apply (e₀ : AuxiliaryIso I n m m')
    (g : AuxiliaryAut.ordered I n m) :
    (e₀.permFiberEquiv.symm g : AuxiliaryIso I n m m') = (g : AuxiliaryAut I n m).trans e₀ :=
  (rfl)

/-- **Finiteness of the arrows.**  If there are finitely many auxiliary labels and the source has
finitely many ordered automorphisms, then there are finitely many arrows between two curves with
unordered auxiliary marks.  In particular the automorphism group `AuxiliaryAut I n m` is then
finite. -/
instance finite [Finite R] [Finite (AuxiliaryAut.ordered I n m)] :
    Finite (AuxiliaryIso I n m m') := by
  have hfiber (π : Equiv.Perm R) : Finite {e : AuxiliaryIso I n m m' // e.perm = π} := by
    rcases isEmpty_or_nonempty {e : AuxiliaryIso I n m m' // e.perm = π} with _ | ⟨e₀, rfl⟩
    · infer_instance
    · exact Finite.of_equiv _ e₀.permFiberEquiv.symm
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv (perm : AuxiliaryIso I n m m' → Equiv.Perm R))

end AuxiliaryIso

/-! ### The groupoid -/

/-- **A nodal curve with `N` distinguished and `R` auxiliary marks**, bundled: normalization
components `X i` indexed by `ι`, flag pairs indexed by `Flag`, and marks labelled by `N ⊕ R`.
The model `I` and the smoothness `n` do not enter the data; they select the arrows of the
groupoid `unorderedAuxiliaryIsomorphismGroupoid`, which are the `C^n` arrows `(π, f)`. -/
structure AuxiliaryMarkedCurve (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (N R : Type*) where
  /-- The index type of the normalization components. -/
  ι : Type u
  /-- The index type of the flag pairs. -/
  Flag : Type v
  /-- The normalization components. -/
  X : ι → Type w
  /-- The topology of each normalization component. -/
  [topologicalSpace : ∀ i, TopologicalSpace (X i)]
  /-- The charts of each normalization component. -/
  [chartedSpace : ∀ i, ChartedSpace H (X i)]
  /-- The gluing data at the flag pairs. -/
  data : FlagPairData ι Flag X
  /-- The distinguished and auxiliary marks. -/
  marking : Marking data (N ⊕ R)

attribute [instance] AuxiliaryMarkedCurve.topologicalSpace AuxiliaryMarkedCurve.chartedSpace

namespace AuxiliaryMarkedCurve

/-- **The groupoid of curves with unordered auxiliary marks.**  Its arrows are the pairs `(π, f)`
of `AuxiliaryIso`, composed by `(ρ, h) ∘ (π, f) = (ρ ∘ π, h ∘ f)`.  Its objects are the same as
those of the groupoid of isomorphisms preserving every label, of which it is the
label-permutation extension, a finite extension when `R` is finite. -/
instance unorderedAuxiliaryIsomorphismGroupoid :
    Groupoid (AuxiliaryMarkedCurve.{u, v, w} I n N R) where
  Hom C C' := AuxiliaryIso I n C.marking C'.marking
  id C := AuxiliaryIso.refl I n C.marking
  comp e e' := AuxiliaryIso.trans e e'
  id_comp := AuxiliaryIso.refl_trans
  comp_id := AuxiliaryIso.trans_refl
  assoc := AuxiliaryIso.trans_assoc
  inv := AuxiliaryIso.symm
  inv_comp := AuxiliaryIso.symm_trans_self
  comp_inv := AuxiliaryIso.self_trans_symm

variable {C C' C'' : AuxiliaryMarkedCurve.{u, v, w} I n N R}

/-- The identity arrow of the groupoid is the identity arrow `(1, id)`. -/
theorem id_def (C : AuxiliaryMarkedCurve.{u, v, w} I n N R) :
    𝟙 C = AuxiliaryIso.refl I n C.marking :=
  (rfl)

/-- Composition in the groupoid is composition of arrows `(π, f)`. -/
theorem comp_def (e : C ⟶ C') (e' : C' ⟶ C'') :
    e ≫ e' = AuxiliaryIso.trans (m' := C'.marking) e e' :=
  (rfl)

/-- The inverse in the groupoid is the inverse arrow `(π⁻¹, f⁻¹)`. -/
theorem inv_def (e : C ⟶ C') : Groupoid.inv e = AuxiliaryIso.symm (m := C.marking) e :=
  (rfl)

end AuxiliaryMarkedCurve

end NodalGluing

end TauCeti
