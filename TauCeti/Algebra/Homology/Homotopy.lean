/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import TauCeti.Algebra.Homology.HomologicalComplex

/-!
# Constructions on chain homotopies

Three constructions of chain homotopies: two produce new homotopies from old ones, and the
third assembles a null-homotopy from components given all at once.

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
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace Homotopy

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
def idPow (h : Homotopy (𝟙 K) s) (m : ℕ) : Homotopy (𝟙 K) (End.of s ^ m) where
  hom i j := ∑ k ∈ Finset.range m, (End.of s ^ k).f i ≫ h.hom i j
  zero i j hij := by simp [h.zero i j hij]
  comm i := by
    have hdn : dNext i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).f i ≫ dNext i h.hom := by
      simpa only [Finset.sum_fn, dNext_comp_left] using
        map_sum (dNext i) (fun k a b ↦ (End.of s ^ k).f a ≫ h.hom a b) (Finset.range m)
    have hpv : prevD i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).f i ≫ prevD i h.hom := by
      simpa only [Finset.sum_fn, prevD_comp_left] using
        map_sum (prevD i) (fun k a b ↦ (End.of s ^ k).f a ≫ h.hom a b) (Finset.range m)
    have hstep : ∀ k ∈ Finset.range m, (End.of s ^ k).f i ≫ dNext i h.hom +
        (End.of s ^ k).f i ≫ prevD i h.hom =
        (End.of s ^ k).f i - (End.of s ^ (k + 1)).f i := fun k _ ↦ by
      have hsum : dNext i h.hom + prevD i h.hom = 𝟙 (K.X i) - s.f i := by
        have hc := h.comm i
        rw [HomologicalComplex.id_f] at hc
        rw [hc]
        abel
      rw [← Preadditive.comp_add, hsum, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.pow_f_succ]
    rw [hdn, hpv, ← Finset.sum_add_distrib, Finset.sum_congr rfl hstep,
      Finset.sum_range_sub' (fun k ↦ (End.of s ^ k).f i) m, pow_zero, End.one_def,
      HomologicalComplex.id_f]
    abel

@[simp]
lemma idPow_hom (h : Homotopy (𝟙 K) s) (m : ℕ) (i j : ι) :
    (h.idPow m).hom i j = ∑ k ∈ Finset.range m, (End.of s ^ k).f i ≫ h.hom i j := (rfl)

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
