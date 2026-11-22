/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.Fiber
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.FiniteProjective
public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic

/-!
# Local constancy of the Euler characteristic on the fibres

Let `R` be a Noetherian ring, `X` a scheme over `R` and `M` a quasi-coherent sheaf on `X` which
is flat over `R` and whose cohomology modules `Hⁿ(X, M)` are finitely generated, as for a
coherent sheaf flat over `R` on a proper scheme. For a prime `p` of `R`, write
`X_p = X ×_R κ(p)` for the fibre and `M_p` for the pullback of `M` to it. Then the Euler
characteristic `p ↦ χ(X_p, M_p) = ∑ᵢ (-1)ⁱ dim_{κ(p)} Hⁱ(X_p, M_p)` is a locally constant
function on `Spec R`, although the individual dimensions `dim_{κ(p)} Hⁱ(X_p, M_p)` are in general
only upper semicontinuous
(`TauCeti.AlgebraicGeometry.upperSemicontinuous_finrank_cohomology_fiber`).
In particular it is constant when `Spec R` is connected.

The cohomology of every fibre is computed by a single bounded complex `P` of finite projective
`R`-modules, `Hⁱ(X_p, M_p) ≅ Hⁱ(κ(p) ⊗_R P)`
(`TauCeti.AlgebraicGeometry.exists_finite_projective_complex_cohomology_pullback`). By
Euler–Poincaré over `κ(p)`, the Euler characteristic of `κ(p) ⊗_R P` is the alternating sum of the
ranks of the terms of `P` at `p`, which are locally constant
(`CochainComplex.isLocallyConstant_homologyEulerChar_fiber`).

The Euler characteristic is read as the truncated alternating sum
`Scheme.Modules.eulerCharBelow κ(p) X_p M_p n = ∑_{i < n} (-1)ⁱ dim_{κ(p)} Hⁱ(X_p, M_p)`. This is
the whole Euler characteristic as soon as the fibre cohomology vanishes in degrees `≥ n`: for
instance when `X` is covered by `N ≤ n` opens with affine nonempty finite intersections, as in
`isLocallyConstant_eulerCharBelow_fiber_of_card_le`, or when the fibres are curves and
`n = 2`. The truncated sum is not locally constant without such a vanishing: for `n = 1` it is
`dim H⁰(X_p, M_p)`, which jumps in general.

The fibres are the concrete pullbacks `pullback (X ↘ Spec R) (Spec κ(p) ⟶ Spec R)`, as in
`TauCeti.AlgebraicGeometry.upperSemicontinuous_finrank_cohomology_fiber`.

## Main results

* `TauCeti.AlgebraicGeometry.isLocallyConstant_eulerCharBelow_fiber_of_card_le`: for a
  cover of `X` by `N` opens with affine nonempty finite intersections and `N ≤ n`, the Euler
  characteristic `p ↦ ∑_{i < n} (-1)ⁱ dim_{κ(p)} Hⁱ(X_p, M_p)` is locally constant on `Spec R`.
* `TauCeti.AlgebraicGeometry.isLocallyConstant_eulerCharBelow_fiber`: for `X`
  quasi-compact with affine diagonal, the same holds for every `n` beyond which the cohomology of
  every fibre vanishes.

## References

* D. Mumford, *Abelian Varieties*, §5, Corollary (b).
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.12.8 and its proof.
* [The Stacks Project, Lemma 0B9T](https://stacks.math.columbia.edu/tag/0B9T).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Module
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  (M : X.Modules) [M.IsQuasicoherent]

/-- For a finite cover `U` of `X` by `N` opens with affine nonempty finite intersections, the
truncated alternating sum `∑_{i < n} (-1)ⁱ dim Hⁱ(X_p, M_p)` is locally constant in `p` as soon as
the fibre cohomology vanishes in the degrees `n ≤ m < N`. Beyond `N` it vanishes automatically,
since the cohomology of every fibre is computed by a complex concentrated in degrees `< N`. -/
private lemma isLocallyConstant_eulerCharBelow_fiber_aux [IsNoetherianRing R]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤)
    (hM : ∀ x : X, Module.Flat R (M.presheaf.stalk x))
    (hfin : ∀ n, Module.Finite R (Cohomology M n)) (n : ℕ)
    (hn : ∀ (p : PrimeSpectrum R) (m : ℕ), n ≤ m → m < Nat.card ι →
      Subsingleton (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) m)) :
    IsLocallyConstant fun p : PrimeSpectrum R ↦
      eulerCharBelow p.asIdeal.ResidueField (pullback (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))
        ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
          (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) n := by
  let : LinearOrder ι := LinearOrder.lift' _ (Finite.equivFin ι).injective
  obtain ⟨P, -, hP₀, hP₁, hP, -, -, hPY⟩ :=
    exists_finite_projective_complex_cohomology_pullback U M hU hcover hM hfin
  convert P.isLocallyConstant_homologyEulerChar_fiber (fun i ↦ (hP i).1) 0 (Nat.card ι - 1)
    (fun i ↦ (hP i).2) using 2 with p
  let κ := p.asIdeal.ResidueField
  let L := ((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  -- The cohomology of the fibre is the homology of `κ(p) ⊗_R P`, in every degree `m : ℕ`.
  have hfinrank (m : ℕ) : finrank κ (L.homology m) = finrank κ (Cohomology
      ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R κ))))).obj M) m) := by
    obtain ⟨e⟩ := hPY κ (pullback (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) _ (IsPullback.of_hasPullback _ _) m
    exact e.finrank_eq
  -- Both sides are sums over the degrees `0 ≤ i < max n N`, which contain the support of the
  -- homology of `κ(p) ⊗_R P`, concentrated in degrees `0, …, N - 1`.
  let k := max n (Nat.card ι)
  have hsupport : GradedObject.finrankSupport (fun i ↦ L.homology i) ⊆
      ((Finset.range k).map Nat.castEmbedding : Finset ℤ) := by
    intro i hi
    have hi : i ∈ Finset.Icc 0 _ :=
      HomologicalComplex.finrankSupport_homology_subset_Icc L 0 (Nat.card ι - 1) hi
    obtain ⟨hi₀, hi₁⟩ := Finset.mem_Icc.mp hi
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi₀
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    exact ⟨m, by omega, rfl⟩
  have hsum (n' : ℕ) : eulerCharBelow κ (pullback (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
      ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R κ))))).obj M) n' =
        ∑ i ∈ Finset.range n', (-1) ^ i * (finrank κ (L.homology i) : ℤ) := by
    induction n' with
    | zero => simp
    | succ n' ih => rw [eulerCharBelow_succ, ih, Finset.sum_range_succ, hfinrank]
  rw [hsum, HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset L _
    hsupport, Finset.sum_map]
  simp only [Nat.castEmbedding_apply, ComplexShape.eulerCharSignsUpInt_χ,
    Int.coe_negOnePow_natCast]
  -- The terms in degrees `n ≤ m < max n N` vanish by hypothesis.
  refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _)) fun m hm hmn ↦ ?_
  simp only [Finset.mem_range, k] at hm hmn
  have := hn p m (by omega) (by omega)
  rw [hfinrank, finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

/-- **Local constancy of the Euler characteristic on the fibres.** Let `R` be a Noetherian ring,
`X` a scheme over `R` covered by `N` opens with affine nonempty finite intersections, and `M` a
quasi-coherent sheaf on `X` with stalks flat over `R` and finitely generated cohomology modules.
Then for every `n ≥ N` the Euler characteristic
`p ↦ χ(X_p, M_p) = ∑_{i < n} (-1)ⁱ dim_{κ(p)} Hⁱ(X_p, M_p)` of the fibres `X_p = X ×_R κ(p)` is a
locally constant function on `Spec R`. -/
theorem isLocallyConstant_eulerCharBelow_fiber_of_card_le [IsNoetherianRing R]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤)
    (hM : ∀ x : X, Module.Flat R (M.presheaf.stalk x))
    (hfin : ∀ n, Module.Finite R (Cohomology M n)) {n : ℕ} (hn : Nat.card ι ≤ n) :
    IsLocallyConstant fun p : PrimeSpectrum R ↦
      eulerCharBelow p.asIdeal.ResidueField (pullback (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))
        ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
          (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) n :=
  isLocallyConstant_eulerCharBelow_fiber_aux M U hU hcover hM hfin n
    fun _ _ h₁ h₂ ↦ absurd (h₂.trans_le hn) (not_lt.mpr h₁)

/-- **Local constancy of the Euler characteristic on the fibres.** Let `R` be a Noetherian ring,
`X` a quasi-compact scheme over `R` with affine diagonal, for instance a separated one, and `M` a
quasi-coherent sheaf on `X` with stalks flat over `R` and finitely generated cohomology modules.
If the cohomology of every fibre `X_p = X ×_R κ(p)` vanishes in degrees `≥ n`, then its Euler
characteristic `p ↦ χ(X_p, M_p) = ∑_{i < n} (-1)ⁱ dim_{κ(p)} Hⁱ(X_p, M_p)` is a locally constant
function on `Spec R`. -/
theorem isLocallyConstant_eulerCharBelow_fiber [IsNoetherianRing R] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hM : ∀ x : X, Module.Flat R (M.presheaf.stalk x))
    (hfin : ∀ n, Module.Finite R (Cohomology M n)) (n : ℕ)
    (hn : ∀ (p : PrimeSpectrum R) (m : ℕ), n ≤ m →
      Subsingleton (Cohomology ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) m)) :
    IsLocallyConstant fun p : PrimeSpectrum R ↦
      eulerCharBelow p.asIdeal.ResidueField (pullback (X ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))
        ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of R))
          (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).obj M) n := by
  -- A finite affine open cover has affine finite intersections, as `X` has affine diagonal.
  let 𝒰 := X.affineCover.finiteSubcover
  exact isLocallyConstant_eulerCharBelow_fiber_aux M (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange)
    (fun s hs ↦ IsAffineOpen.finset_inf s hs fun i _ ↦ isAffineOpen_opensRange (𝒰.f i))
    𝒰.iSup_opensRange hM hfin n fun p m h _ ↦ hn p m h

end TauCeti.AlgebraicGeometry
