/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum

/-!
# Cyclic factors of glue alphabets

Conway--Sloane display the discriminant group of a reducible root system as a product of cyclic
groups, one or two per component, in the component order: `ℤ/(n+1)` for `Aₙ`, `(ℤ/2)²` for `Dₙ`
with `n` even, `ℤ/4` for `Dₙ` with `n` odd, `ℤ/3` for `E₆`, `ℤ/2` for `E₇`, and nothing for `E₈`.
This file records those orders as the list `TauCeti.DynkinType.glueCyclicFactors` and proves that
the glue alphabet of a component, and the module of glue words of a finite ordered family of
components, are additively equivalent to the corresponding products of `ZMod` factors.  Through
`TauCeti.DynkinType.glueWordIsometry`, the same holds for the actual discriminant group of the
orthogonal sum of the root lattices.

A product of cyclic groups with orders `l : List ℕ` is written `(i : Fin l.length) → ZMod l[i]`.
The factors of a family `t : Fin n → DynkinType` are concatenated in the order of the components,
`(List.ofFn fun i ↦ (t i).glueCyclicFactors).flatten`, so that this list can be compared with a
displayed presentation by evaluation.

The equivalences are additive only: the quadratic forms are not part of the displayed
presentation, and are retained by the glue alphabets themselves.

## Main declarations

* `TauCeti.DynkinType.glueCyclicFactors`: the orders of the displayed cyclic factors of the glue
  alphabet of a Dynkin type.
* `TauCeti.DynkinType.nonempty_addEquiv_glueAlphabet`: the glue alphabet is additively the
  product of its cyclic factors.
* `TauCeti.DynkinType.nonempty_addEquiv_pi_glueAlphabet`: the same for the glue words of a
  finite ordered family of components.
* `TauCeti.DynkinType.nonempty_addEquiv_discriminantGroup_pi_rootLattice`: the same for the
  discriminant group of the orthogonal sum of the component root lattices.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8,
  and Chapter 16, Table 16.1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

/-- **The cyclic factors of a glue alphabet**: the orders of the cyclic groups whose product is
the glue alphabet of a simply-laced Dynkin type in the Conway--Sloane display, namely `[n + 1]`
for `Aₙ`, `[2, 2]` for `Dₙ` with `n` even, `[4]` for `Dₙ` with `n` odd, `[3]` for `E₆`, `[2]` for
`E₇` and the empty list for `E₈` (`TauCeti.DynkinType.nonempty_addEquiv_glueAlphabet`).  The
non-simply-laced types, which have no glue alphabet, are sent to the empty list. -/
@[expose] def glueCyclicFactors : DynkinType → List ℕ
  | A n => [n + 1]
  | D n => if Even n then [2, 2] else [4]
  | E6 => [3]
  | E7 => [2]
  | _ => []

/-- The glue alphabet of `Aₙ` is the single cyclic factor `ℤ/(n+1)`. -/
@[simp]
theorem glueCyclicFactors_A (n : ℕ) : (A n).glueCyclicFactors = [n + 1] :=
  (rfl)

/-- For even `n`, the glue alphabet of `Dₙ` has two cyclic factors of order two. -/
@[simp]
theorem glueCyclicFactors_D_of_even {n : ℕ} (hn : Even n) : (D n).glueCyclicFactors = [2, 2] :=
  ite_eq_left hn

/-- For odd `n`, the glue alphabet of `Dₙ` is the single cyclic factor `ℤ/4`. -/
@[simp]
theorem glueCyclicFactors_D_of_odd {n : ℕ} (hn : Odd n) : (D n).glueCyclicFactors = [4] :=
  ite_eq_right (Nat.not_even_iff_odd.mpr hn)

/-- The glue alphabet of `E₆` is the single cyclic factor `ℤ/3`. -/
@[simp]
theorem glueCyclicFactors_E6 : E6.glueCyclicFactors = [3] :=
  (rfl)

/-- The glue alphabet of `E₇` is the single cyclic factor `ℤ/2`. -/
@[simp]
theorem glueCyclicFactors_E7 : E7.glueCyclicFactors = [2] :=
  (rfl)

/-- The glue alphabet of `E₈` is trivial and has no cyclic factors. -/
@[simp]
theorem glueCyclicFactors_E8 : E8.glueCyclicFactors = [] :=
  (rfl)

/-- The glue alphabet of a component, placed in front of a product of cyclic groups with orders
`L`, is the product of cyclic groups with orders `t.glueCyclicFactors ++ L`.  The tail `L` lets
families of components be treated by induction, and the free list `F` lets the factors of `Dₙ` be
rewritten by parity before they are substituted into the type. -/
private theorem nonempty_addEquiv_glueAlphabet_prod (t : DynkinType) (ht : t.IsSimplyLaced)
    (L F : List ℕ) (hF : t.glueCyclicFactors ++ L = F) :
    Nonempty (t.glueAlphabet ht × ((i : Fin L.length) → ZMod L[i]) ≃+
      ((i : Fin F.length) → ZMod F[i])) := by
  -- Prepending a cyclic factor of order `a` to a product of cyclic groups with orders `l`.
  have cons (a : ℕ) (l : List ℕ) : ZMod a × ((i : Fin l.length) → ZMod l[i]) ≃+
      ((i : Fin (a :: l).length) → ZMod (a :: l)[i]) :=
    (Fin.consLinearEquiv ℤ fun i : Fin (l.length + 1) ↦ ZMod (a :: l)[i]).toAddEquiv
  cases t with
  | A n => subst hF; exact ⟨cons (n + 1) L⟩
  | D n =>
    rcases Nat.even_or_odd n with hn | hn
    · rw [glueCyclicFactors_D_of_even hn] at hF
      subst hF
      rw [glueAlphabet_D_of_even n ht hn]
      exact ⟨AddEquiv.prodAssoc.trans
        (((AddEquiv.refl (ZMod 2)).prodCongr (cons 2 L)).trans (cons 2 (2 :: L)))⟩
    · rw [glueCyclicFactors_D_of_odd hn] at hF
      subst hF
      rw [glueAlphabet_D_of_odd n ht hn]
      exact ⟨cons 4 L⟩
  | E6 => subst hF; exact ⟨cons 3 L⟩
  | E7 => subst hF; exact ⟨cons 2 L⟩
  | E8 =>
    subst hF
    have : Unique (E8.glueAlphabet ht) := inferInstanceAs (Unique (ZMod 1))
    exact ⟨AddEquiv.uniqueProd⟩
  | B n => exact (not_isSimplyLaced_B n ht).elim
  | C n => exact (not_isSimplyLaced_C n ht).elim
  | F4 => exact (not_isSimplyLaced_F4 ht).elim
  | G2 => exact (not_isSimplyLaced_G2 ht).elim

/-- **The glue alphabet is a product of cyclic groups**: the glue alphabet of a simply-laced
Dynkin type is additively equivalent to the product of `ZMod` factors with orders
`t.glueCyclicFactors`. -/
theorem nonempty_addEquiv_glueAlphabet (t : DynkinType) (ht : t.IsSimplyLaced) :
    Nonempty (t.glueAlphabet ht ≃+
      ((i : Fin t.glueCyclicFactors.length) → ZMod t.glueCyclicFactors[i])) := by
  have : IsEmpty (Fin ([] : List ℕ).length) := Fin.isEmpty'
  obtain ⟨e⟩ := nonempty_addEquiv_glueAlphabet_prod t ht [] _ (List.append_nil _)
  exact ⟨AddEquiv.prodUnique.symm.trans e⟩

/-- The glue words of a family of components, placed in front of a product of cyclic groups with
orders `L`, form the product of cyclic groups with the concatenated factors of the components
followed by `L`. -/
private theorem nonempty_addEquiv_pi_glueAlphabet_prod :
    ∀ {n : ℕ} (t : Fin n → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced) (L F : List ℕ),
      (List.ofFn fun i ↦ (t i).glueCyclicFactors).flatten ++ L = F →
      Nonempty ((FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) ×
          ((i : Fin L.length) → ZMod L[i]) ≃+ ((i : Fin F.length) → ZMod F[i]))
  | 0, t, ht, L, F, hF => by
    have : Unique (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) :=
      Pi.uniqueOfIsEmpty _
    rw [List.ofFn_zero, List.flatten_nil, List.nil_append] at hF
    subst hF
    exact ⟨AddEquiv.uniqueProd⟩
  | n + 1, t, ht, L, F, hF => by
    obtain ⟨e⟩ := nonempty_addEquiv_pi_glueAlphabet_prod (fun i ↦ t i.succ) (fun i ↦ ht i.succ)
      L _ rfl
    obtain ⟨e₀⟩ := nonempty_addEquiv_glueAlphabet_prod (t 0) (ht 0) _ F
      (by rw [← hF, List.ofFn_succ, List.flatten_cons, List.append_assoc])
    exact ⟨(((Fin.consLinearEquiv ℤ fun i ↦ (t i).glueAlphabet (ht i)).symm.toAddEquiv.prodCongr
      (AddEquiv.refl _)).trans AddEquiv.prodAssoc).trans
        (((AddEquiv.refl _).prodCongr e).trans e₀)⟩

/-- **The glue words of a family of components form a product of cyclic groups**: for a finite
ordered family `t` of simply-laced components, the module of glue words is additively equivalent
to the product of `ZMod` factors whose orders `l` are the cyclic factors of the components, in the
order of the components.  The list `l` is a parameter so that it can be supplied in a displayed
form, together with a proof that it evaluates to the concatenated cyclic factors. -/
theorem nonempty_addEquiv_pi_glueAlphabet {n : ℕ} (t : Fin n → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) {l : List ℕ}
    (hl : (List.ofFn fun i ↦ (t i).glueCyclicFactors).flatten = l) :
    Nonempty ((FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)) ≃+
      ((i : Fin l.length) → ZMod l[i])) := by
  have : IsEmpty (Fin ([] : List ℕ).length) := Fin.isEmpty'
  obtain ⟨e⟩ := nonempty_addEquiv_pi_glueAlphabet_prod t ht [] l ((List.append_nil _).trans hl)
  exact ⟨AddEquiv.prodUnique.symm.trans e⟩

/-- **The discriminant group of an orthogonal sum of root lattices is a product of cyclic
groups**: for a finite ordered family `t` of valid simply-laced components, the discriminant group
of `⊥ i, (t i).rootLattice` is additively equivalent to the product of `ZMod` factors whose orders
`l` are the cyclic factors of the components, in the order of the components. -/
theorem nonempty_addEquiv_discriminantGroup_pi_rootLattice {n : ℕ} (t : Fin n → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) (hv : ∀ i, (t i).Valid) {l : List ℕ}
    (hl : (List.ofFn fun i ↦ (t i).glueCyclicFactors).flatten = l) :
    Nonempty ((pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup ≃+
      ((i : Fin l.length) → ZMod l[i])) := by
  obtain ⟨e⟩ := nonempty_addEquiv_pi_glueAlphabet t ht hl
  exact ⟨(glueWordIsometry t ht hv).toLinearEquiv.toAddEquiv.symm.trans e⟩

end TauCeti.DynkinType
