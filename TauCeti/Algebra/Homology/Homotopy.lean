/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Constructions on chain homotopies

Constructions of chain homotopies, including composition of homotopy-commutative squares,
transport and iteration of homotopies, and assembly of null-homotopies from components.

`Homotopy.compSquare` composes specified square homotopies by postcomposing the first
and precomposing the second, retaining their sum rather than choosing a new outer homotopy.

`Homotopy.descCokernel` descends a homotopy along a degreewise cokernel.  Let `p : L ⟶ M` exhibit
`M` in each degree as the cokernel of `u : K ⟶ L`, and let `p' : L' ⟶ M'` be any morphism of
complexes.  A chain homotopy between morphisms `L ⟶ L'` whose components send the image of `u`
into the kernel of `p'` then descends to a chain homotopy between the induced morphisms `M ⟶ M'`.
Only the source side is assumed to be a degreewise cokernel; on the target side the hypothesis is
the bare vanishing `u.f i ≫ HL.hom i j ≫ p'.f j = 0`, which is what the universal property needs.
This is the mechanism behind homotopy invariance of relative homology, where `M` is the relative
chain complex of a pair, that is, the degreewise cokernel of the chains of the subspace, and the
vanishing holds because the homotopy restricts to the subspace.

`Homotopy.idPow` iterates a chain homotopy from the identity of `K` to an endomorphism `s`: it
exhibits every power `sᵐ` as homotopic to the identity, through the explicit operator
`∑_{k < m} sᵏ ≫ h`.  Its components are needed, and not just the existence of some homotopy, when
`m` is allowed to vary from one summand of `K` to another, as in the proof that small singular
chains for an open cover include as a chain homotopy equivalence.

`Homotopy.mkChainComplex` builds a null-homotopy of a chain map between `ℕ`-indexed chain
complexes from its components `h n : P.X n ⟶ Q.X (n + 1)`, given all at once together with the
homotopy identities in degree zero and in positive degrees.  It is the non-inductive counterpart of
Mathlib's `Homotopy.mkInductive`, for the situation where the components are constructed by a
recursion of their own rather than one degree at a time from the previous two.

`Homotopy.mkCochainComplexInt` is its counterpart for `ℤ`-indexed cochain complexes: a
null-homotopy of `e : P ⟶ Q` from components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy
identities `e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`, stated in every degree `n + 1` so that no
index is a difference.

`Homotopy.comm_zero_apply` and `Homotopy.comm_succ_apply` are the homotopy identities of a
homotopy between maps of `ℕ`-indexed chain complexes of modules, evaluated on elements.

`CochainComplex.nonempty_homotopy_mkHomToSingle_zero_iff` characterizes null-homotopic chain maps
from a cochain complex `K` to an object `A` placed in degree `i`: the map given by `φ : Kⁱ ⟶ A` is
null-homotopic if and only if `φ` factors through the differential `Kⁱ ⟶ Kⁱ⁺¹`. It is Mathlib's
criterion `CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff`, translated from
coboundaries to homotopies.
Dually, `CochainComplex.nonempty_homotopy_zero_iff_of_single` characterizes null-homotopic chain
maps from an object `X` placed in degree `p` to a cochain complex `K`: such a map is null-homotopic
if and only if its component `X ⟶ Kᵖ` factors through the differential `Kᵖ⁻¹ ⟶ Kᵖ`.

`Homotopy.cyclesMap_sub_eq` expresses the difference of the maps on cycles induced by
homotopic maps as a factorization through a term of the target complex. In particular, these
maps agree after passing to a stable category that kills that term.

`Homotopy.acyclic` says that a contractible complex, one whose identity is null-homotopic, is
acyclic.

`HomotopyEquiv.ofHomotopyRetract` and `HomotopyEquiv.ofHomotopyRetractOfComm` transfer a homotopy
equivalence `e : HomotopyEquiv K₁ L₁` to a morphism `i₂ : K₂ ⟶ L₂` that is a retract up to homotopy
of `e.hom`, with transferred inverse `rL ≫ e.inv ≫ jK` and without assuming any homotopy on the
composites `jK ≫ rK` or `jL ≫ rL`.

`HomotopyEquiv.homotopyInvSquare` shows that a homotopy-commutative square between the forward maps
of two homotopy equivalences induces a homotopy-commutative square in the opposite direction between
their homotopy inverses, and hence a commutative square on homology via `toHomologyIso`. Taking
identity vertical maps, `HomotopyEquiv.homotopyInv` shows that two homotopy equivalences with
homotopic forward maps have homotopic inverses and induce the same isomorphism on homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace Homotopy

section Squares

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type*} {c : ComplexShape ι}
  {K₁ L₁ K₂ L₂ K₃ L₃ : HomologicalComplex C c}
  {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {φ₃ : K₃ ⟶ L₃}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} {a' : K₂ ⟶ K₃} {b' : L₂ ⟶ L₃}

/-- Compose two specified homotopy-commutative squares. The homotopy is the sum of the
postcomposition of the first homotopy and the precomposition of the second. -/
def compSquare (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))
    (H' : Homotopy (φ₂ ≫ b') (a' ≫ φ₃)) :
    Homotopy (φ₁ ≫ (b ≫ b')) ((a ≫ a') ≫ φ₃) :=
  (Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    ((H.compRight b').trans
      ((Homotopy.ofEq (Category.assoc _ _ _)).trans
        ((H'.compLeft a).trans (Homotopy.ofEq (Category.assoc _ _ _).symm))))

@[simp]
lemma compSquare_hom (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))
    (H' : Homotopy (φ₂ ≫ b') (a' ≫ φ₃)) (p q : ι) :
    (H.compSquare H').hom p q = H.hom p q ≫ b'.f q + a.f p ≫ H'.hom p q := by
  simp [compSquare]

end Squares

/-- On cycles, the difference of homotopic maps factors through the preceding target term.
This identity does not require exactness of either complex. -/
theorem cyclesMap_sub_eq {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} {f g : K ⟶ L}
    (h : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.cyclesMap f i - HomologicalComplex.cyclesMap g i =
      K.iCycles i ≫ h.hom i (c.prev i) ≫ L.toCycles (c.prev i) i := by
  apply (cancel_mono (L.iCycles i)).mp
  simp only [Preadditive.sub_comp, HomologicalComplex.cyclesMap_i, Category.assoc,
    HomologicalComplex.toCycles_i]
  rw [h.comm i]
  simp [dNext, prevD, Preadditive.comp_add, ← Category.assoc]

/-- A contractible complex is acyclic. -/
lemma acyclic {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K : HomologicalComplex C c} [∀ i, K.HasHomology i]
    (h : Homotopy (𝟙 K) 0) : K.Acyclic := fun i ↦ by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using
    h.homologyMap_eq i

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L M L' M' : HomologicalComplex C c}
  {fL gL : L ⟶ L'} {fM gM : M ⟶ M'}
  (HL : Homotopy fL gL)
  (u : K ⟶ L) (p : L ⟶ M) (p' : L' ⟶ M')
  (hw : ∀ i, u.f i ≫ p.f i = 0)
  (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p.f i) (hw i)))
  (hcomm : ∀ i j, u.f i ≫ HL.hom i j ≫ p'.f j = 0)

include hw hp hcomm

/-- The components of the chain homotopy that `Homotopy.descCokernel` obtains on the quotient
complex `M`. -/
@[no_expose]
def descCokernelHom (i j : ι) : M.X i ⟶ M'.X j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).1

@[reassoc (attr := simp)]
lemma π_descCokernelHom (i j : ι) :
    p.f i ≫ descCokernelHom HL u p p' hw hp hcomm i j = HL.hom i j ≫ p'.f j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).2

private lemma π_comp_dNext (i : ι) :
    p.f i ≫ dNext i (descCokernelHom HL u p p' hw hp hcomm) = dNext i HL.hom ≫ p'.f i := by
  rw [← dNext_comp_left, ← dNext_comp_right]
  exact congrArg (fun F ↦ dNext i F) (by funext a b; exact π_descCokernelHom ..)

private lemma π_comp_prevD (i : ι) :
    p.f i ≫ prevD i (descCokernelHom HL u p p' hw hp hcomm) = prevD i HL.hom ≫ p'.f i := by
  rw [← prevD_comp_left, ← prevD_comp_right]
  exact congrArg (fun F ↦ prevD i F) (by funext a b; exact π_descCokernelHom ..)

/-- A chain homotopy on the total complexes whose components kill the subcomplex after composing
with `p'` descends to a chain homotopy on the quotient complex `M`. -/
@[no_expose]
def descCokernel (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') : Homotopy fM gM where
  hom := descCokernelHom HL u p p' hw hp hcomm
  zero i j hij := Cofork.IsColimit.hom_ext (hp i) (by simp [HL.zero i j hij])
  comm i := Cofork.IsColimit.hom_ext (hp i) (by
    simp only [Cofork.π_ofπ, Preadditive.comp_add, π_comp_dNext, π_comp_prevD,
      ← HomologicalComplex.comp_f p fM, ← HomologicalComplex.comp_f p gM, hf, hg,
      HomologicalComplex.comp_f]
    rw [← Preadditive.add_comp, ← Preadditive.add_comp, ← HL.comm i])

@[simp]
lemma descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') :
    (descCokernel HL u p p' hw hp hcomm hf hg).hom = descCokernelHom HL u p p' hw hp hcomm := (rfl)

@[reassoc]
lemma π_descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') (i j : ι) :
    p.f i ≫ (descCokernel HL u p p' hw hp hcomm hf hg).hom i j = HL.hom i j ≫ p'.f j :=
  π_descCokernelHom HL u p p' hw hp hcomm i j

end Homotopy

section Pow

variable {C : Type u} [Category.{v} C] {ι : Type*} {c : ComplexShape ι}

namespace Homotopy

variable [Preadditive C] {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Iterating a chain homotopy from the identity.  If `h` is a chain homotopy from the identity of
`K` to a chain endomorphism `s`, then `h.idPow m` is a chain homotopy from the identity to the
`m`-th power of `s`, whose operator in bidegree `(i, j)` is `∑_{k < m} (sᵏ)ᵢ ≫ hᵢⱼ`. -/
@[no_expose]
def idPow (h : Homotopy (𝟙 K) s) (m : ℕ) : Homotopy (𝟙 K) (End.of s ^ m).asHom where
  hom i j := ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j
  zero i j hij := by simp [h.zero i j hij]
  comm i := by
    have hdn : dNext i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom := by
      simpa only [Finset.sum_fn, dNext_comp_left] using
        map_sum (dNext i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hpv : prevD i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ prevD i h.hom := by
      simpa only [Finset.sum_fn, prevD_comp_left] using
        map_sum (prevD i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hstep : ∀ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom +
        (End.of s ^ k).asHom.f i ≫ prevD i h.hom =
        (End.of s ^ k).asHom.f i - (End.of s ^ (k + 1)).asHom.f i := fun k _ ↦ by
      have hsum : dNext i h.hom + prevD i h.hom = 𝟙 (K.X i) - s.f i := by
        have hc := h.comm i
        rw [HomologicalComplex.id_f] at hc
        rw [hc]
        abel
      rw [← Preadditive.comp_add, hsum, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.pow_f_succ]
    rw [hdn, hpv, ← Finset.sum_add_distrib, Finset.sum_congr rfl hstep,
      Finset.sum_range_sub' (fun k ↦ (End.of s ^ k).asHom.f i) m, pow_zero, End.one_asHom,
      HomologicalComplex.id_f]
    abel

@[simp]
lemma idPow_hom (h : Homotopy (𝟙 K) s) (m : ℕ) (i j : ι) :
    (h.idPow m).hom i j = ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j := (rfl)

end Homotopy

end Pow

section MkChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : ChainComplex C ℕ}

namespace Homotopy

/-- A null-homotopy of a chain map `e : P ⟶ Q` between `ℕ`-indexed chain complexes, from its
components `h n : P.X n ⟶ Q.X (n + 1)` and the homotopy identities `e.f 0 = h 0 ≫ d` and
`e.f (n + 1) = d ≫ h n + h (n + 1) ≫ d`. The components are given all at once; compare
`Homotopy.mkInductive`, which constructs them one degree at a time. -/
@[no_expose]
def mkChainComplex (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1)) (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : i + 1 = j then h i ≫ eqToHom (congrArg Q.X hij) else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.down_Rel] using hij)
  comm i := by
    cases i with
    | zero =>
        rw [dNext_zero_chainComplex, prevD_chainComplex]
        simpa using comm_zero
    | succ i =>
        rw [dNext_succ_chainComplex, prevD_chainComplex]
        simpa using comm_succ i

@[simp]
lemma mkChainComplex_hom_succ (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1))
    (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1))
    (n : ℕ) : (mkChainComplex e h comm_zero comm_succ).hom n (n + 1) = h n := by
  simp [mkChainComplex]

end Homotopy

end MkChainComplex

section MkCochainComplexInt

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : CochainComplex C ℤ}

namespace Homotopy

/-- A null-homotopy of a map `e : P ⟶ Q` between `ℤ`-indexed cochain complexes, from its
components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy identities
`e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`. Every degree is written as `n + 1`, so that no index is
ever a difference. The components are given all at once, as in `Homotopy.mkChainComplex`. -/
@[no_expose]
def mkCochainComplexInt (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : j + 1 = i then eqToHom (congrArg P.X hij.symm) ≫ h j else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.up_Rel] using hij)
  comm i := by
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk n (n + 1) rfl)]
    simpa using comm n

@[simp]
lemma mkCochainComplexInt_hom (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1))
    (n : ℤ) : (mkCochainComplexInt e h comm).hom (n + 1) n = h n := by
  simp [mkCochainComplexInt]

end Homotopy

end MkCochainComplexInt

section ModuleCat

variable {R : Type*} [Ring R] {P Q : ChainComplex (ModuleCat R) ℕ} {e e' : P ⟶ Q}

namespace Homotopy

/-- The homotopy identity in degree zero, on elements: the difference of the two maps is the
boundary of the homotopy. -/
theorem comm_zero_apply (h : Homotopy e e') (x : P.X 0) :
    e.f 0 x = Q.d 1 0 (h.hom 0 1 x) + e'.f 0 x := by
  have hc := h.comm 0
  rw [dNext_zero_chainComplex, prevD_chainComplex, zero_add] at hc
  simpa using congrArg (fun φ : P.X 0 ⟶ Q.X 0 ↦ φ x) hc

/-- The homotopy identity in positive degrees, on elements. -/
theorem comm_succ_apply (h : Homotopy e e') (n : ℕ) (x : P.X (n + 1)) :
    e.f (n + 1) x =
      h.hom n (n + 1) (P.d (n + 1) n x) + Q.d (n + 2) (n + 1) (h.hom (n + 1) (n + 2) x) +
        e'.f (n + 1) x := by
  have hc := h.comm (n + 1)
  rw [dNext_succ_chainComplex, prevD_chainComplex] at hc
  simpa [add_assoc] using congrArg (fun φ : P.X (n + 1) ⟶ Q.X (n + 1) ↦ φ x) hc

/-- On a cycle, the difference of homotopic maps is the boundary of the homotopy. -/
theorem d_hom_apply_of_d_eq_zero (h : Homotopy e e') {n : ℕ} (x : P.X n)
    (hx : P.d n (n - 1) x = 0) :
    Q.d (n + 1) n (h.hom n (n + 1) x) = e.f n x - e'.f n x := by
  cases n with
  | zero =>
    exact eq_sub_iff_add_eq.mpr (h.comm_zero_apply x).symm
  | succ n =>
    have hx' : P.d (n + 1) n x = 0 := by simpa using hx
    have hc := h.comm_succ_apply n x
    rw [hx', map_zero, zero_add] at hc
    exact eq_sub_iff_add_eq.mpr hc.symm

end Homotopy

end ModuleCat

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

open HomComplex in
/-- **Null-homotopic chain maps to an object in one degree**: the chain map from `K` to `A`
placed in degree `i` given by `φ : Kⁱ ⟶ A` is null-homotopic if and only if `φ` factors through
the differential `Kⁱ ⟶ Kʲ`, where `j = i + 1`. -/
lemma nonempty_homotopy_mkHomToSingle_zero_iff (K : CochainComplex C ℤ) {i j : ℤ}
    (hij : i + 1 = j) {A : C} (φ : K.X i ⟶ A)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel k i → K.d k i ≫ φ = 0) :
    Nonempty (Homotopy (HomologicalComplex.mkHomToSingle φ hφ) 0) ↔
      ∃ g : K.X j ⟶ A, K.d i j ≫ g = φ := by
  have hφ' : K.d (i - 1) i ≫ φ = 0 := hφ _ (by simp)
  rw [← Cocycle.toSingleMk_mem_coboundaries_iff φ (add_zero i) (i - 1) (by lia) hφ' j hij,
    mem_coboundaries_iff _ (-1) (by simp)]
  -- The cocycle of `Cocycle.toSingleMk` is the zero-cochain of the chain map.
  have h : (Cocycle.toSingleMk φ (add_zero i) (i - 1) (by lia) hφ' : Cochain _ _ 0) =
      Cochain.ofHom (HomologicalComplex.mkHomToSingle φ hφ) :=
    (Cochain.toSingleEquiv (add_zero i)).injective (by
      simp [Cochain.toSingleEquiv, HomologicalComplex.mkHomToSingle_f])
  rw [h]
  exact ⟨fun ⟨ho⟩ ↦ ⟨Cochain.ofHomotopy ho, by simp [δ_ofHomotopy]⟩,
    fun ⟨z, hz⟩ ↦ ⟨(Cochain.equivHomotopy _ _).symm ⟨z, by simpa using hz.symm⟩⟩⟩

open HomComplex in
/-- **Null-homotopic chain maps from an object in one degree**: a chain map `χ` from `X` placed
in degree `p` to `K` is null-homotopic if and only if its component `X ⟶ Kᵖ` factors through the
differential `Kᵠ ⟶ Kᵖ`, where `q + 1 = p`. -/
lemma nonempty_homotopy_zero_iff_of_single (K : CochainComplex C ℤ) {X : C} {p q : ℤ}
    (hqp : q + 1 = p) (χ : (singleFunctor C p).obj X ⟶ K) :
    Nonempty (Homotopy χ 0) ↔
      ∃ g : X ⟶ K.X q, g ≫ K.d q p =
        (HomologicalComplex.singleObjXSelf (.up ℤ) p X).inv ≫ χ.f p := by
  have hf : ((HomologicalComplex.singleObjXSelf (.up ℤ) p X).inv ≫ χ.f p) ≫ K.d p (p + 1) = 0 := by
    rw [Category.assoc, χ.comm]
    simp
  rw [← Cocycle.fromSingleMk_mem_coboundaries_iff _ (add_zero p) (p + 1) rfl hf q hqp,
    mem_coboundaries_iff _ (-1) (by simp)]
  -- The cocycle of `Cocycle.fromSingleMk` is the zero-cochain of `χ`.
  have h : (Cocycle.fromSingleMk _ (add_zero p) (p + 1) rfl hf : Cochain _ _ 0) =
      Cochain.ofHom χ :=
    (Cochain.fromSingleEquiv (add_zero p)).injective (by simp [Cochain.fromSingleEquiv_apply])
  rw [h]
  exact ⟨fun ⟨ho⟩ ↦ ⟨Cochain.ofHomotopy ho, by simp [δ_ofHomotopy]⟩,
    fun ⟨z, hz⟩ ↦ ⟨(Cochain.equivHomotopy _ _).symm ⟨z, by simpa using hz.symm⟩⟩⟩

end CochainComplex

namespace HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}

section Retract

variable {K₁ L₁ K₂ L₂ : HomologicalComplex C c}

/-- Transfer a homotopy equivalence `e : HomotopyEquiv K₁ L₁` to a morphism `i₂ : K₂ ⟶ L₂`
along maps `jK : K₁ ⟶ K₂`, `jL : L₁ ⟶ L₂`, `rK : K₂ ⟶ K₁`, and `rL : L₂ ⟶ L₁` exhibiting `i₂`
as a retract up to homotopy of `e.hom`: homotopy-commutative squares `jK ≫ i₂ ~ e.hom ≫ jL` and
`i₂ ≫ rL ~ rK ≫ e.hom`, together with homotopies `rK ≫ jK ~ 𝟙 K₂` and `rL ≫ jL ~ 𝟙 L₂`.
The transferred homotopy inverse is `rL ≫ e.inv ≫ jK`; no homotopies on `jK ≫ rK` or `jL ≫ rL`
are used. -/
def ofHomotopyRetract (e : HomotopyEquiv K₁ L₁) (i₂ : K₂ ⟶ L₂)
    {jK : K₁ ⟶ K₂} {jL : L₁ ⟶ L₂} {rK : K₂ ⟶ K₁} {rL : L₂ ⟶ L₁}
    (hK : Homotopy (rK ≫ jK) (𝟙 K₂)) (hL : Homotopy (rL ≫ jL) (𝟙 L₂))
    (hj : Homotopy (jK ≫ i₂) (e.hom ≫ jL)) (hr : Homotopy (i₂ ≫ rL) (rK ≫ e.hom)) :
    HomotopyEquiv K₂ L₂ where
  hom := i₂
  inv := rL ≫ e.inv ≫ jK
  homotopyHomInvId :=
    (Homotopy.ofEq (Category.assoc i₂ rL (e.inv ≫ jK)).symm).trans
      ((hr.compRight (e.inv ≫ jK)).trans
        ((Homotopy.ofEq (by simp only [Category.assoc])).trans
          (((e.homotopyHomInvId.compRight jK).compLeft rK).trans
            ((Homotopy.ofEq (by simp only [Category.id_comp])).trans hK))))
  homotopyInvHomId :=
    (Homotopy.ofEq (by simp only [Category.assoc])).trans
      (((hj.compLeft e.inv).compLeft rL).trans
        ((Homotopy.ofEq (by simp only [Category.assoc])).trans
          (((e.homotopyInvHomId.compRight jL).compLeft rL).trans
            ((Homotopy.ofEq (by simp only [Category.id_comp])).trans hL))))

/-- The forward morphism of `ofHomotopyRetract` is `i₂`. -/
@[simp]
lemma ofHomotopyRetract_hom (e : HomotopyEquiv K₁ L₁) (i₂ : K₂ ⟶ L₂)
    {jK : K₁ ⟶ K₂} {jL : L₁ ⟶ L₂} {rK : K₂ ⟶ K₁} {rL : L₂ ⟶ L₁}
    (hK : Homotopy (rK ≫ jK) (𝟙 K₂)) (hL : Homotopy (rL ≫ jL) (𝟙 L₂))
    (hj : Homotopy (jK ≫ i₂) (e.hom ≫ jL)) (hr : Homotopy (i₂ ≫ rL) (rK ≫ e.hom)) :
    (e.ofHomotopyRetract i₂ hK hL hj hr).hom = i₂ :=
  (rfl)

/-- The homotopy inverse of `ofHomotopyRetract` is `rL ≫ e.inv ≫ jK`. -/
@[simp]
lemma ofHomotopyRetract_inv (e : HomotopyEquiv K₁ L₁) (i₂ : K₂ ⟶ L₂)
    {jK : K₁ ⟶ K₂} {jL : L₁ ⟶ L₂} {rK : K₂ ⟶ K₁} {rL : L₂ ⟶ L₁}
    (hK : Homotopy (rK ≫ jK) (𝟙 K₂)) (hL : Homotopy (rL ≫ jL) (𝟙 L₂))
    (hj : Homotopy (jK ≫ i₂) (e.hom ≫ jL)) (hr : Homotopy (i₂ ≫ rL) (rK ≫ e.hom)) :
    (e.ofHomotopyRetract i₂ hK hL hj hr).inv = rL ≫ e.inv ≫ jK :=
  (rfl)

/-- Transfer a homotopy equivalence `e : HomotopyEquiv K₁ L₁` to a morphism `i₂ : K₂ ⟶ L₂` along
strictly commutative squares `jK ≫ i₂ = e.hom ≫ jL` and `i₂ ≫ rL = rK ≫ e.hom` with homotopies
`rK ≫ jK ~ 𝟙 K₂` and `rL ≫ jL ~ 𝟙 L₂`. -/
def ofHomotopyRetractOfComm (e : HomotopyEquiv K₁ L₁) (i₂ : K₂ ⟶ L₂)
    {jK : K₁ ⟶ K₂} {jL : L₁ ⟶ L₂} {rK : K₂ ⟶ K₁} {rL : L₂ ⟶ L₁}
    (hK : Homotopy (rK ≫ jK) (𝟙 K₂)) (hL : Homotopy (rL ≫ jL) (𝟙 L₂))
    (hj : jK ≫ i₂ = e.hom ≫ jL) (hr : i₂ ≫ rL = rK ≫ e.hom) :
    HomotopyEquiv K₂ L₂ :=
  e.ofHomotopyRetract i₂ hK hL (.ofEq hj) (.ofEq hr)

/-- The forward morphism of `ofHomotopyRetractOfComm` is `i₂`. -/
@[simp]
lemma ofHomotopyRetractOfComm_hom (e : HomotopyEquiv K₁ L₁) (i₂ : K₂ ⟶ L₂)
    {jK : K₁ ⟶ K₂} {jL : L₁ ⟶ L₂} {rK : K₂ ⟶ K₁} {rL : L₂ ⟶ L₁}
    (hK : Homotopy (rK ≫ jK) (𝟙 K₂)) (hL : Homotopy (rL ≫ jL) (𝟙 L₂))
    (hj : jK ≫ i₂ = e.hom ≫ jL) (hr : i₂ ≫ rL = rK ≫ e.hom) :
    (e.ofHomotopyRetractOfComm i₂ hK hL hj hr).hom = i₂ :=
  (rfl)

/-- The homotopy inverse of `ofHomotopyRetractOfComm` is `rL ≫ e.inv ≫ jK`. -/
@[simp]
lemma ofHomotopyRetractOfComm_inv (e : HomotopyEquiv K₁ L₁) (i₂ : K₂ ⟶ L₂)
    {jK : K₁ ⟶ K₂} {jL : L₁ ⟶ L₂} {rK : K₂ ⟶ K₁} {rL : L₂ ⟶ L₁}
    (hK : Homotopy (rK ≫ jK) (𝟙 K₂)) (hL : Homotopy (rL ≫ jL) (𝟙 L₂))
    (hj : jK ≫ i₂ = e.hom ≫ jL) (hr : i₂ ≫ rL = rK ≫ e.hom) :
    (e.ofHomotopyRetractOfComm i₂ hK hL hj hr).inv = rL ≫ e.inv ≫ jK :=
  (rfl)

/-- Along the trivial identity retract, `ofHomotopyRetractOfComm` leaves the homotopy inverse
unchanged. -/
lemma ofHomotopyRetractOfComm_id_inv (e : HomotopyEquiv K₁ L₁) :
    (e.ofHomotopyRetractOfComm e.hom
      (Homotopy.ofEq (Category.id_comp (𝟙 K₁))) (Homotopy.ofEq (Category.id_comp (𝟙 L₁)))
      (by simp) (by simp)).inv = e.inv := by
  simp

/-- Along the trivial identity retract, `ofHomotopyRetractOfComm` preserves the operator of
`homotopyHomInvId` in every bidegree. -/
lemma ofHomotopyRetractOfComm_id_homotopyHomInvId_hom (e : HomotopyEquiv K₁ L₁) (p q : ι) :
    (e.ofHomotopyRetractOfComm e.hom
      (Homotopy.ofEq (Category.id_comp (𝟙 K₁))) (Homotopy.ofEq (Category.id_comp (𝟙 L₁)))
      (by simp) (by simp)).homotopyHomInvId.hom p q = e.homotopyHomInvId.hom p q := by
  simp [ofHomotopyRetractOfComm, ofHomotopyRetract]

/-- Along the trivial identity retract, `ofHomotopyRetractOfComm` preserves the operator of
`homotopyInvHomId` in every bidegree. -/
lemma ofHomotopyRetractOfComm_id_homotopyInvHomId_hom (e : HomotopyEquiv K₁ L₁) (p q : ι) :
    (e.ofHomotopyRetractOfComm e.hom
      (Homotopy.ofEq (Category.id_comp (𝟙 K₁))) (Homotopy.ofEq (Category.id_comp (𝟙 L₁)))
      (by simp) (by simp)).homotopyInvHomId.hom p q = e.homotopyInvHomId.hom p q := by
  simp [ofHomotopyRetractOfComm, ofHomotopyRetract]

end Retract

section InverseUniqueness

variable {K L K₁ L₁ K₂ L₂ : HomologicalComplex C c}

/-- **Homotopy naturality of homotopy inverses.** Given homotopy equivalences `e₁` and `e₂` and a
homotopy `fK ≫ e₂.hom ~ e₁.hom ≫ fL`, the composites `fL ≫ e₂.inv` and `e₁.inv ≫ fK` are
homotopic via `fL ≫ e₂.inv ~ e₁.inv ≫ e₁.hom ≫ fL ≫ e₂.inv ~ e₁.inv ≫ fK ≫ e₂.hom ≫ e₂.inv ~
e₁.inv ≫ fK`. -/
def homotopyInvSquare (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂)
    {fK : K₁ ⟶ K₂} {fL : L₁ ⟶ L₂} (h : Homotopy (fK ≫ e₂.hom) (e₁.hom ≫ fL)) :
    Homotopy (fL ≫ e₂.inv) (e₁.inv ≫ fK) :=
  (Homotopy.ofEq (Category.id_comp (fL ≫ e₂.inv)).symm).trans
    ((e₁.homotopyInvHomId.symm.compRight (fL ≫ e₂.inv)).trans
      ((Homotopy.ofEq (by simp only [Category.assoc])).trans
        (((h.symm.compRight e₂.inv).compLeft e₁.inv).trans
          ((Homotopy.ofEq (by simp only [Category.assoc])).trans
            (e₂.homotopyHomInvId.compLeftId (e₁.inv ≫ fK))))))

/-- A commutative square between the forward maps of two homotopy equivalences induces a
homotopy-commutative square between their homotopy inverses. -/
def homotopyInvOfComm (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂)
    {fK : K₁ ⟶ K₂} {fL : L₁ ⟶ L₂} (h : fK ≫ e₂.hom = e₁.hom ≫ fL) :
    Homotopy (fL ≫ e₂.inv) (e₁.inv ≫ fK) :=
  e₁.homotopyInvSquare e₂ (.ofEq h)

/-- **Uniqueness of homotopy inverses up to homotopy.** Two homotopy equivalences whose forward
maps are homotopic have homotopic inverse maps (`e₁.inv ~ e₁.inv ≫ e₂.hom ≫ e₂.inv ~
e₁.inv ≫ e₁.hom ≫ e₂.inv ~ e₂.inv`). -/
def homotopyInv (e₁ e₂ : HomotopyEquiv K L) (h : Homotopy e₁.hom e₂.hom) :
    Homotopy e₁.inv e₂.inv :=
  (Homotopy.ofEq (Category.id_comp e₁.inv).symm).trans
    ((e₂.homotopyInvSquare e₁
      ((Homotopy.ofEq (Category.id_comp e₁.hom)).trans
        (h.trans (Homotopy.ofEq (Category.comp_id e₂.hom).symm)))).trans
      (Homotopy.ofEq (Category.comp_id e₂.inv)))

/-- Two homotopy equivalences with the same forward map have homotopic inverse maps. -/
def homotopyInvOfHomEq (e₁ e₂ : HomotopyEquiv K L) (h : e₁.hom = e₂.hom) :
    Homotopy e₁.inv e₂.inv :=
  e₁.homotopyInv e₂ (.ofEq h)

/-- The forward morphism of `toHomologyIso` is `homologyMap e.hom`. -/
@[simp]
lemma toHomologyIso_hom (e : HomotopyEquiv K L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    (e.toHomologyIso i).hom = HomologicalComplex.homologyMap e.hom i :=
  (rfl)

/-- The inverse morphism of `toHomologyIso` is `homologyMap e.inv`. -/
@[simp]
lemma toHomologyIso_inv (e : HomotopyEquiv K L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    (e.toHomologyIso i).inv = HomologicalComplex.homologyMap e.inv i :=
  (rfl)

/-- Two homotopy equivalences whose forward maps are homotopic induce the same isomorphism on
homology. -/
lemma toHomologyIso_eq_of_homotopy {e₁ e₂ : HomotopyEquiv K L} (h : Homotopy e₁.hom e₂.hom)
    (i : ι) [K.HasHomology i] [L.HasHomology i] :
    e₁.toHomologyIso i = e₂.toHomologyIso i :=
  Iso.ext (h.homologyMap_eq i)

/-- Two homotopy equivalences with the same forward map induce the same isomorphism on homology. -/
lemma toHomologyIso_eq_of_hom_eq {e₁ e₂ : HomotopyEquiv K L} (h : e₁.hom = e₂.hom)
    (i : ι) [K.HasHomology i] [L.HasHomology i] :
    e₁.toHomologyIso i = e₂.toHomologyIso i :=
  toHomologyIso_eq_of_homotopy (.ofEq h) i

/-- **Naturality of the inverse homology isomorphism.** A homotopy-commutative square between the
forward maps of two homotopy equivalences commutes on homology with the inverses of
`toHomologyIso`. -/
@[reassoc]
lemma homologyMap_comp_toHomologyIso_inv (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂)
    {fK : K₁ ⟶ K₂} {fL : L₁ ⟶ L₂} (h : Homotopy (fK ≫ e₂.hom) (e₁.hom ≫ fL)) (i : ι)
    [K₁.HasHomology i] [L₁.HasHomology i] [K₂.HasHomology i] [L₂.HasHomology i] :
    HomologicalComplex.homologyMap fL i ≫ (e₂.toHomologyIso i).inv =
      (e₁.toHomologyIso i).inv ≫ HomologicalComplex.homologyMap fK i := by
  simp only [toHomologyIso_inv, ← HomologicalComplex.homologyMap_comp]
  exact (e₁.homotopyInvSquare e₂ h).homologyMap_eq i

/-- A commutative square between the forward maps of two homotopy equivalences commutes on homology
with the inverses of `toHomologyIso`. -/
@[reassoc]
lemma homologyMap_comp_toHomologyIso_inv_of_comm (e₁ : HomotopyEquiv K₁ L₁)
    (e₂ : HomotopyEquiv K₂ L₂) {fK : K₁ ⟶ K₂} {fL : L₁ ⟶ L₂}
    (h : fK ≫ e₂.hom = e₁.hom ≫ fL) (i : ι)
    [K₁.HasHomology i] [L₁.HasHomology i] [K₂.HasHomology i] [L₂.HasHomology i] :
    HomologicalComplex.homologyMap fL i ≫ (e₂.toHomologyIso i).inv =
      (e₁.toHomologyIso i).inv ≫ HomologicalComplex.homologyMap fK i :=
  e₁.homologyMap_comp_toHomologyIso_inv e₂ (.ofEq h) i

end InverseUniqueness

end HomotopyEquiv
