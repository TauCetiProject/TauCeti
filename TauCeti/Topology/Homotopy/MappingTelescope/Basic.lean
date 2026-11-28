/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import TauCeti.Topology.Homotopy.MappingCylinder

/-!
# The mapping telescope of a sequence of continuous maps

Given a sequence of spaces `X : ℕ → Type u` and continuous bonding maps
`f : ∀ n, C(X n, X (n + 1))`, the *mapping telescope* `TauCeti.MappingTelescope f` is the homotopy
colimit obtained from the disjoint union of cylinders `Σ n, I × X n` by gluing the top face
`{1} × X n` of the `n`-th cylinder to the bottom face `{0} × X (n + 1)` of the next cylinder along
`f n`.

Every point of the disjoint union has a unique normal representative of height strictly less than
`1`: a top-face point `⟨n, 1, x⟩` is replaced by `⟨n + 1, 0, f n x⟩` and every other point is
left unchanged. Taking the quotient by the kernel of this normalization—following the presentation
of `TauCeti.MappingCylinder`—makes all point-set identifications immediate
(`TauCeti.MappingTelescope.mkCyl_eq_mkCyl_iff`) without chaining an inductive equivalence relation
across multiple cylinders.

Each space `X n` embeds as a closed subspace of the telescope as the bottom face `{0} × X n` of
its cylinder (`TauCeti.MappingTelescope.isClosedEmbedding_incl`), each segment embeds as a closed
copy of `TauCeti.MappingCylinder (f n)`
(`TauCeti.MappingTelescope.isClosedEmbedding_fromMappingCylinder`), and the `n`-th cylinder
supplies the canonical homotopy from `incl f n` to `(incl f (n + 1)).comp (f n)`
(`TauCeti.MappingTelescope.inclHomotopy`). Separation (`T1Space` and `T2Space`) and compact
generation (`UCompactlyGeneratedSpace` and `CompactlyGeneratedSpace`) pass from the stages `X n`
directly to `TauCeti.MappingTelescope f` with no auxiliary coreflection.

## Main declarations

* `TauCeti.MappingTelescope`: the mapping telescope of `f : ∀ n, C(X n, X (n + 1))`, with cylinder
  maps `TauCeti.MappingTelescope.mkCyl`, stage inclusions `TauCeti.MappingTelescope.incl`, and
  quotient presentation `TauCeti.MappingTelescope.isQuotientMap_sigma_mkCyl`.
* `TauCeti.MappingTelescope.lift`: the universal property out of the mapping telescope, accompanied
  by `TauCeti.MappingTelescope.hom_ext`, `TauCeti.MappingTelescope.ind`, and the product continuity
  criterion `TauCeti.MappingTelescope.continuous_prod_iff`.
* `TauCeti.MappingTelescope.isClosedEmbedding_incl` and
  `TauCeti.MappingTelescope.isClosedEmbedding_fromMappingCylinder`: closed embeddings of each stage
  and of each individual mapping cylinder into the telescope.
* `TauCeti.MappingTelescope.bondOfLE`, `TauCeti.MappingTelescope.inclHomotopy`, and
  `TauCeti.MappingTelescope.inclHomotopyOfLE`: composite bonding maps and canonical homotopies
  relating stage inclusions.
* `T1Space`, `T2Space`, and `UCompactlyGeneratedSpace` instances on `TauCeti.MappingTelescope f`.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.F and Appendix, Proposition A.11.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 14.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

universe u v w

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]

/-- Normal form on `Σ n, I × X n` for the mapping telescope of `f`: a point `(1, x)` on the top
face of the `n`-th cylinder is sent to `(0, f n x)` on the bottom face of the `(n + 1)`-st
cylinder, and every point of height different from `1` is fixed. Because `0 ≠ 1` in `I`, this map
is idempotent and two points have the same normal form precisely when the telescope gluing
identifies them. -/
private def telescopeNormalize (f : ∀ n, C(X n, X (n + 1))) (a : Σ n, I × X n) : Σ n, I × X n :=
  if a.2.1 = 1 then ⟨a.1 + 1, (0, f a.1 a.2.2)⟩ else a

/-- The **mapping telescope** of a sequence of continuous maps `f : ∀ n, C(X n, X (n + 1))`: the
disjoint union of cylinders `Σ n, I × X n` with `(1, x)` in `I × X n` identified with
`(0, f n x)` in `I × X (n + 1)`.

The quotient presentation is private to this file; callers construct points via
`TauCeti.MappingTelescope.mkCyl` and `TauCeti.MappingTelescope.incl`, eliminate via
`TauCeti.MappingTelescope.lift` and `TauCeti.MappingTelescope.ind`, and prove map equality via
`TauCeti.MappingTelescope.hom_ext`. -/
def MappingTelescope (f : ∀ n, C(X n, X (n + 1))) : Type u :=
  Quotient (Setoid.ker (telescopeNormalize f))

namespace MappingTelescope

variable {f : ∀ n, C(X n, X (n + 1))}

@[no_expose] instance : TopologicalSpace (MappingTelescope f) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (telescopeNormalize f))))

/-- The map sending a point of the `n`-th cylinder `I × X n` to its class in the mapping
telescope. -/
def mkCyl (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(I × X n, MappingTelescope f) :=
  ⟨fun p => Quotient.mk _ ⟨n, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The inclusion of the `n`-th space `X n` into the mapping telescope as the bottom face
`{0} × X n` of the `n`-th cylinder. -/
def incl (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(X n, MappingTelescope f) :=
  (mkCyl f n).comp ⟨fun x => (0, x), by fun_prop⟩

@[simp]
lemma incl_apply (n : ℕ) (x : X n) : incl f n x = mkCyl f n (0, x) := (rfl)

private lemma mkCyl_eq_mkCyl_iff' {m n : ℕ} {p : I × X m} {q : I × X n} :
    mkCyl f m p = mkCyl f n q ↔ telescopeNormalize f ⟨m, p⟩ = telescopeNormalize f ⟨n, q⟩ :=
  Quotient.eq (r := Setoid.ker (telescopeNormalize f))

/-- The top face `{1} × X n` of the `n`-th cylinder is glued to the bottom face `{0} × X (n + 1)`
of the `(n + 1)`-st cylinder along `f n`. -/
@[simp]
lemma mkCyl_one (n : ℕ) (x : X n) : mkCyl f n (1, x) = mkCyl f (n + 1) (0, f n x) :=
  mkCyl_eq_mkCyl_iff'.2 (by simp [telescopeNormalize])

/-- Complete point-identification criterion in the mapping telescope: two cylinder points agree
if and only if they are identical, both lie on the top face of the same cylinder with the same
image under `f`, or one lies on a top face and the other is its glued image on the next bottom
face. -/
@[simp]
lemma mkCyl_eq_mkCyl_iff {m n : ℕ} {s t : I} {x : X m} {y : X n} :
    mkCyl f m (s, x) = mkCyl f n (t, y) ↔
      (∃ h : m = n, s = t ∧ h ▸ x = y) ∨
      (∃ h : m = n, s = 1 ∧ t = 1 ∧ f n (h ▸ x) = f n y) ∨
      (∃ h : m + 1 = n, s = 1 ∧ t = 0 ∧ h ▸ f m x = y) ∨
      (∃ h : n + 1 = m, s = 0 ∧ t = 1 ∧ x = h ▸ f n y) := by
  rw [mkCyl_eq_mkCyl_iff']
  simp only [telescopeNormalize]
  split_ifs with hs ht ht
  · refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨hm, hxy⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl : m = n := by omega
      exact Or.inr (Or.inl ⟨rfl, hs, ht, by simpa using hxy⟩)
    · rintro (⟨rfl, -, rfl⟩ | ⟨rfl, -, -, hxy⟩ | ⟨rfl, -, ht0, -⟩ | ⟨rfl, hs0, -, -⟩)
      · rfl
      · exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl hxy))
      · exact absurd (ht.symm.trans ht0) one_ne_zero
      · exact absurd (hs.symm.trans hs0) one_ne_zero
  · refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 h
      obtain ⟨ht0, hfy⟩ := Prod.mk.inj (eq_of_heq hxy)
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hs, ht0.symm, hfy⟩))
    · rintro (⟨rfl, hst, -⟩ | ⟨-, -, ht1, -⟩ | ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, _, ht1, -⟩)
      exacts [absurd (hst.symm.trans hs) ht, absurd ht1 ht, rfl, absurd ht1 ht]
  · refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 h
      obtain ⟨hs0, hfy⟩ := Prod.mk.inj (eq_of_heq hxy)
      exact Or.inr (Or.inr (Or.inr ⟨rfl, hs0, ht, hfy⟩))
    · rintro (⟨rfl, hst, -⟩ | ⟨-, hs1, -, -⟩ | ⟨rfl, hs1, -, -⟩ | ⟨rfl, rfl, -, rfl⟩)
      exacts [absurd (hst.trans ht) hs, absurd hs1 hs, absurd hs1 hs, rfl]
  · refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 h
      obtain ⟨hst, hxy⟩ := Prod.mk.inj (eq_of_heq hxy)
      exact Or.inl ⟨rfl, hst, hxy⟩
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨-, hs1, -⟩ | ⟨-, hs1, -⟩ | ⟨-, -, ht1, -⟩)
      exacts [rfl, absurd hs1 hs, absurd hs1 hs, absurd ht1 ht]

lemma mkCyl_eq_mkCyl_same_iff {n : ℕ} {s t : I} {x y : X n} :
    mkCyl f n (s, x) = mkCyl f n (t, y) ↔
      (s = t ∧ x = y) ∨ (s = 1 ∧ t = 1 ∧ f n x = f n y) := by
  rw [mkCyl_eq_mkCyl_iff']
  simp only [telescopeNormalize]
  split_ifs with hs ht ht <;> simp_all [Prod.ext_iff, eq_comm]

lemma incl_inj {n : ℕ} {x y : X n} : incl f n x = incl f n y ↔ x = y := by
  simp [incl_apply]

lemma incl_injective (n : ℕ) : Function.Injective (incl f n) := fun _ _ => incl_inj.1

lemma incl_eq_incl_iff {m n : ℕ} {x : X m} {y : X n} :
    incl f m x = incl f n y ↔ ∃ h : m = n, h ▸ x = y := by
  simp only [incl_apply, mkCyl_eq_mkCyl_iff, zero_ne_one, false_and, and_false, exists_false,
    or_false, true_and]

/-- Induction principle for points of the mapping telescope. -/
@[elab_as_elim]
lemma ind {p : MappingTelescope f → Prop} (cyl : ∀ (n : ℕ) (q : I × X n), p (mkCyl f n q))
    (z : MappingTelescope f) : p z := by
  induction z using Quotient.ind with
  | _ a => exact cyl a.1 a.2

/-- Every point of the mapping telescope has a representative of height strictly less than `1`. -/
@[elab_as_elim]
lemma ind_ne_one {p : MappingTelescope f → Prop}
    (cyl : ∀ (n : ℕ) (s : I) (x : X n), s ≠ 1 → p (mkCyl f n (s, x)))
    (z : MappingTelescope f) : p z := by
  induction z using ind with
  | cyl n q =>
    obtain ⟨s, x⟩ := q
    by_cases hs : s = 1
    · subst hs
      rw [mkCyl_one]
      exact cyl (n + 1) 0 (f n x) zero_ne_one
    · exact cyl n s x hs

/-- **The mapping telescope is a quotient of `Σ n, I × X n`.** -/
theorem isQuotientMap_sigma_mkCyl :
    IsQuotientMap fun p : Σ n, I × X n => mkCyl f p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A subset of the mapping telescope is open if and only if its preimage in every cylinder is
open. -/
theorem isOpen_iff {U : Set (MappingTelescope f)} :
    IsOpen U ↔ ∀ n, IsOpen (mkCyl f n ⁻¹' U) := by
  rw [← isQuotientMap_sigma_mkCyl.isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A subset of the mapping telescope is closed if and only if its preimage in every cylinder is
closed. -/
theorem isClosed_iff {S : Set (MappingTelescope f)} :
    IsClosed S ↔ ∀ n, IsClosed (mkCyl f n ⁻¹' S) := by
  rw [← isQuotientMap_sigma_mkCyl.isClosed_preimage, isClosed_sigma_iff]
  rfl

section Lift

variable {W : Type w} [TopologicalSpace W] {g : ∀ n, C(I × X n, W)}

private lemma sigma_telescopeNormalize (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x))
    (a : Σ n, I × X n) :
    (fun b : Σ n, I × X n => g b.1 b.2) (telescopeNormalize f a) = g a.1 a.2 := by
  obtain ⟨n, s, x⟩ := a
  by_cases hs : s = 1
  · subst hs
    rw [show telescopeNormalize f ⟨n, 1, x⟩ = ⟨n + 1, 0, f n x⟩ by simp [telescopeNormalize], hg]
  · rw [show telescopeNormalize f ⟨n, s, x⟩ = ⟨n, s, x⟩ by simp [telescopeNormalize, hs]]

/-- **Universal property of the mapping telescope.** A family of continuous maps on the cylinders
`I × X n` that agree along each gluing `g n (1, x) = g (n + 1) (0, f n x)` descends to a continuous
map out of the mapping telescope. -/
def lift (g : ∀ n, C(I × X n, W)) (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) :
    C(MappingTelescope f, W) :=
  ⟨Quotient.lift (fun a : Σ n, I × X n => g a.1 a.2) fun a b hab => by
      rw [← sigma_telescopeNormalize hg a, ← sigma_telescopeNormalize hg b, hab],
    Continuous.quotient_lift (continuous_sigma fun n => (g n).continuous) _⟩

@[simp]
lemma lift_mkCyl (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) (n : ℕ) (p : I × X n) :
    lift g hg (mkCyl f n p) = g n p := (rfl)

lemma lift_incl (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) (n : ℕ) (x : X n) :
    lift g hg (incl f n x) = g n (0, x) := (rfl)

/-- **Extensionality for maps out of the mapping telescope.** -/
@[ext]
theorem hom_ext {F G : C(MappingTelescope f, W)}
    (hcyl : ∀ (n : ℕ) (p : I × X n), F (mkCyl f n p) = G (mkCyl f n p)) : F = G := by
  refine ContinuousMap.ext fun z => ?_
  induction z using ind with
  | cyl n p => exact hcyl n p

/-- **Uniqueness in the universal property of the mapping telescope.** -/
theorem lift_unique (hg : ∀ n x, g n (1, x) = g (n + 1) (0, f n x)) {F : C(MappingTelescope f, W)}
    (hcyl : ∀ (n : ℕ) (p : I × X n), F (mkCyl f n p) = g n p) : F = lift g hg :=
  hom_ext fun n p => by rw [hcyl, lift_mkCyl]

end Lift

/-- **Continuity criterion for maps out of `Z × MappingTelescope f`.** For a locally compact space
`Z`, a map out of `Z × MappingTelescope f` is continuous if and only if its restriction to each
`Z × (I × X n)` is continuous. Taking `Z = I` builds homotopies on the mapping telescope. -/
theorem continuous_prod_iff {Z W : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [TopologicalSpace W] {g : Z × MappingTelescope f → W} :
    Continuous g ↔ ∀ n, Continuous fun q : Z × (I × X n) => g (q.1, mkCyl f n q.2) := by
  refine ⟨fun hg n => hg.comp (by fun_prop), fun h =>
    isQuotientMap_sigma_mkCyl.continuous_lift_prod_right ?_⟩
  rw [← ((Homeomorph.prodComm Z (Σ n, I × X n)).trans
    Homeomorph.sigmaProdDistrib).symm.comp_continuous_iff', continuous_sigma_iff]
  exact fun n => (h n).comp continuous_swap

/-- The canonical real-valued height function on `MappingTelescope f`, sending `mkCyl f n (s, x)`
to `(n : ℝ) + s`. -/
def height (f : ∀ n, C(X n, X (n + 1))) : C(MappingTelescope f, ℝ) :=
  lift (fun n => ⟨fun p => (n : ℝ) + (p.1 : ℝ), continuous_const.add
    (continuous_subtypeVal.comp continuous_fst)⟩) fun n _ => by simp [add_assoc]

@[simp]
theorem height_mkCyl (n : ℕ) (p : I × X n) :
    height f (mkCyl f n p) = (n : ℝ) + (p.1 : ℝ) :=
  lift_mkCyl _ n p

theorem height_incl (n : ℕ) (x : X n) : height f (incl f n x) = n := by
  simp [incl_apply]

section Embeddings

/-- The canonical map from the individual mapping cylinder `MappingCylinder (f n)` into the
mapping telescope, embedding the `n`-th cylinder and its glued base `X (n + 1)`. -/
def fromMappingCylinder (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    C(MappingCylinder (f n), MappingTelescope f) :=
  MappingCylinder.lift (mkCyl f n) (incl f (n + 1)) fun x => mkCyl_one n x

@[simp]
lemma fromMappingCylinder_mkCyl (n : ℕ) (p : I × X n) :
    fromMappingCylinder f n (MappingCylinder.mkCyl (f n) p) = mkCyl f n p :=
  MappingCylinder.lift_mkCyl _ p

@[simp]
lemma fromMappingCylinder_mkBase (n : ℕ) (y : X (n + 1)) :
    fromMappingCylinder f n (MappingCylinder.mkBase (f n) y) = incl f (n + 1) y :=
  MappingCylinder.lift_mkBase _ y

lemma fromMappingCylinder_incl (n : ℕ) (x : X n) :
    fromMappingCylinder f n (MappingCylinder.incl (f n) x) = incl f n x := by
  rw [MappingCylinder.incl_apply, fromMappingCylinder_mkCyl, incl_apply]

@[simp]
lemma fromMappingCylinder_comp_incl (n : ℕ) :
    (fromMappingCylinder f n).comp (MappingCylinder.incl (f n)) = incl f n :=
  ContinuousMap.ext (fromMappingCylinder_incl n)

@[simp]
lemma fromMappingCylinder_comp_mkBase (n : ℕ) :
    (fromMappingCylinder f n).comp (MappingCylinder.mkBase (f n)) = incl f (n + 1) :=
  ContinuousMap.ext (fromMappingCylinder_mkBase n)

private lemma eq_mkBase_of_mkCyl_eq_incl {n : ℕ} {s : I} {x : X n} {y : X (n + 1)}
    (h : mkCyl f n (s, x) = incl f (n + 1) y) :
    MappingCylinder.mkCyl (f n) (s, x) = MappingCylinder.mkBase (f n) y := by
  rw [incl_apply, mkCyl_eq_mkCyl_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, rfl, _, rfl⟩ | ⟨h, -⟩
  exacts [by omega, by omega, MappingCylinder.mkCyl_one x, by omega]

lemma fromMappingCylinder_injective (n : ℕ) : Function.Injective (fromMappingCylinder f n) := by
  intro a b hab
  induction a using MappingCylinder.ind with
  | cyl p =>
    induction b using MappingCylinder.ind with
    | cyl q =>
      rw [fromMappingCylinder_mkCyl, fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_same_iff] at hab
      exact MappingCylinder.mkCyl_eq_mkCyl_iff.2 hab
    | base y =>
      rw [fromMappingCylinder_mkCyl, fromMappingCylinder_mkBase] at hab
      exact eq_mkBase_of_mkCyl_eq_incl hab
  | base y =>
    induction b using MappingCylinder.ind with
    | cyl q =>
      rw [fromMappingCylinder_mkBase, fromMappingCylinder_mkCyl] at hab
      exact (eq_mkBase_of_mkCyl_eq_incl hab.symm).symm
    | base z =>
      rw [fromMappingCylinder_mkBase, fromMappingCylinder_mkBase, incl_inj] at hab
      exact congrArg _ hab

private lemma mem_image_fromMappingCylinder_succ {n : ℕ} {K : Set (MappingCylinder (f n))}
    {s : I} {y : X (n + 1)} :
    mkCyl f (n + 1) (s, y) ∈ fromMappingCylinder f n '' K ↔
      s = 0 ∧ MappingCylinder.mkBase (f n) y ∈ K := by
  refine ⟨?_, fun ⟨hs, hyK⟩ => ⟨MappingCylinder.mkBase (f n) y, hyK, by simp [hs]⟩⟩
  rintro ⟨w, hwK, hw⟩
  induction w using MappingCylinder.ind with
  | cyl q =>
    rw [fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_iff] at hw
    rcases hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, hq1, hs0, rfl⟩ | ⟨h, -⟩
    exacts [by omega, by omega, ⟨hs0, by rwa [← q.eta, hq1, MappingCylinder.mkCyl_one] at hwK⟩,
      by omega]
  | base z =>
    rw [fromMappingCylinder_mkBase, incl_apply, mkCyl_eq_mkCyl_same_iff] at hw
    rcases hw with ⟨hs0, hzy⟩ | ⟨h01, -⟩
    exacts [⟨hs0.symm, hzy ▸ hwK⟩, absurd h01 zero_ne_one]

private lemma mem_image_fromMappingCylinder_pred {m : ℕ} {K : Set (MappingCylinder (f (m + 1)))}
    {s : I} {y : X m} :
    mkCyl f m (s, y) ∈ fromMappingCylinder f (m + 1) '' K ↔
      s = 1 ∧ MappingCylinder.incl (f (m + 1)) (f m y) ∈ K := by
  refine ⟨?_, fun ⟨hs, hyK⟩ => ⟨MappingCylinder.incl (f (m + 1)) (f m y), hyK, by
    rw [hs, fromMappingCylinder_incl, incl_apply, mkCyl_one]⟩⟩
  rintro ⟨w, hwK, hw⟩
  induction w using MappingCylinder.ind with
  | cyl q =>
    rw [fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_iff] at hw
    rcases hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, hq0, hs1, hq2⟩
    exacts [by omega, by omega, by omega,
      ⟨hs1, by rwa [← q.eta, hq0, hq2, ← MappingCylinder.incl_apply] at hwK⟩]
  | base z =>
    rw [fromMappingCylinder_mkBase, incl_apply, mkCyl_eq_mkCyl_iff] at hw
    rcases hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

private lemma preimage_mkCyl_image_fromMappingCylinder (n m : ℕ)
    (K : Set (MappingCylinder (f n))) :
    mkCyl f m ⁻¹' (fromMappingCylinder f n '' K) =
      if h : m = n then h ▸ (MappingCylinder.mkCyl (f n) ⁻¹' K)
      else if h1 : m = n + 1 then
        {p : I × X m | p.1 = 0 ∧ MappingCylinder.mkBase (f n) (h1 ▸ p.2) ∈ K}
      else if h0 : m + 1 = n then
        {p : I × X m | p.1 = 1 ∧ MappingCylinder.incl (f n) (h0 ▸ f m p.2) ∈ K}
      else ∅ := by
  ext ⟨s, y⟩
  simp only [mem_preimage]
  split_ifs with h h1 h0
  · subst h
    rw [← fromMappingCylinder_mkCyl m (s, y), (fromMappingCylinder_injective m).mem_set_image]
    rfl
  · subst h1
    exact mem_image_fromMappingCylinder_succ
  · subst h0
    exact mem_image_fromMappingCylinder_pred
  · simp only [mem_image, mem_empty_iff_false, iff_false, not_exists, not_and]
    intro w _ hw
    induction w using MappingCylinder.ind with
    | cyl q =>
      rw [fromMappingCylinder_mkCyl, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [h rfl, h rfl, h1 rfl, h0 rfl]
    | base z =>
      rw [fromMappingCylinder_mkBase, incl_apply, mkCyl_eq_mkCyl_iff] at hw
      rcases hw with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨_, h01, -⟩ | ⟨h', -⟩
      exacts [h1 rfl, h1 rfl, zero_ne_one h01, by omega]

/-- **Each individual mapping cylinder `MappingCylinder (f n)` embeds as a closed subspace of the
mapping telescope.** -/
theorem isClosedEmbedding_fromMappingCylinder (n : ℕ) :
    IsClosedEmbedding (fromMappingCylinder f n) := by
  refine .of_continuous_injective_isClosedMap (fromMappingCylinder f n).continuous
    (fromMappingCylinder_injective n) fun K hK => isClosed_iff.2 fun m => ?_
  rw [preimage_mkCyl_image_fromMappingCylinder]
  split_ifs with h h1 h0
  · subst h
    exact hK.preimage (MappingCylinder.mkCyl (f m)).continuous
  · subst h1
    exact (isClosed_singleton.preimage continuous_fst).inter
      (hK.preimage ((MappingCylinder.mkBase (f n)).continuous.comp continuous_snd))
  · subst h0
    exact (isClosed_singleton.preimage continuous_fst).inter
      (hK.preimage ((MappingCylinder.incl (f (m + 1))).continuous.comp
        ((f m).continuous.comp continuous_snd)))
  · exact isClosed_empty

/-- The range of `fromMappingCylinder f n` is the union of the `n`-th cylinder with the `(n + 1)`-st
stage inclusion. -/
theorem range_fromMappingCylinder (n : ℕ) :
    Set.range (fromMappingCylinder f n) = Set.range (mkCyl f n) ∪ Set.range (incl f (n + 1)) := by
  ext z
  simp only [mem_range, mem_union]
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    induction w using MappingCylinder.ind with
    | cyl p => exact Or.inl ⟨p, (fromMappingCylinder_mkCyl n p).symm⟩
    | base y => exact Or.inr ⟨y, (fromMappingCylinder_mkBase n y).symm⟩
  · rintro (⟨p, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨MappingCylinder.mkCyl (f n) p, fromMappingCylinder_mkCyl n p⟩
    · exact ⟨MappingCylinder.mkBase (f n) y, fromMappingCylinder_mkBase n y⟩

/-- **Every stage `X n` embeds as a closed subspace of the mapping telescope.** -/
theorem isClosedEmbedding_incl (n : ℕ) : IsClosedEmbedding (incl f n) := by
  rw [← fromMappingCylinder_comp_incl, ContinuousMap.coe_comp]
  exact (isClosedEmbedding_fromMappingCylinder n).comp MappingCylinder.isClosedEmbedding_incl

/-- The image of `X n` in the mapping telescope is closed. -/
theorem isClosed_range_incl (n : ℕ) : IsClosed (Set.range (incl f n)) :=
  (isClosedEmbedding_incl n).isClosed_range

/-- Each stage `X n` is homeomorphic to its image in the mapping telescope. -/
def inclHomeomorph (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : X n ≃ₜ Set.range (incl f n) :=
  (isClosedEmbedding_incl (f := f) n).isEmbedding.toHomeomorph

@[simp]
lemma inclHomeomorph_apply_coe (n : ℕ) (x : X n) :
    (inclHomeomorph f n x : MappingTelescope f) = incl f n x := (rfl)

end Embeddings

section SeparationAndCompactGeneration

/-- If every stage `X n` is `T₁`, then so is the mapping telescope. -/
instance [∀ n, T1Space (X n)] : T1Space (MappingTelescope f) where
  t1 z := by
    induction z using ind_ne_one with
    | cyl n s x hs =>
      by_cases hs0 : s = 0
      · subst hs0
        rw [← incl_apply, ← Set.image_singleton]
        exact (isClosedEmbedding_incl n).isClosedMap _ isClosed_singleton
      · refine isClosed_iff.2 fun m => ?_
        by_cases hmn : m = n
        · subst hmn
          convert isClosed_singleton (x := (s, x)) using 1
          ext ⟨t, y⟩
          simp only [mem_preimage, mem_singleton_iff, mkCyl_eq_mkCyl_same_iff, Prod.mk.injEq]
          exact ⟨by rintro (h | ⟨-, ht1, -⟩); exacts [h, absurd ht1 hs], Or.inl⟩
        · convert isClosed_empty using 1
          ext ⟨t, y⟩
          simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
          intro heq
          rcases mkCyl_eq_mkCyl_iff.1 heq with
            ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨_, -, h0, -⟩ | ⟨_, -, ht1, -⟩
          exacts [hmn rfl, hmn rfl, hs0 h0, hs ht1]

private def cylPred (n : ℕ) (U : Set (X n)) : (Σ m, I × X m) → Prop
  | ⟨m, s, y⟩ => ∃ h : m = n, s ∈ Set.Ioo (0 : I) 1 ∧ h ▸ y ∈ U

private lemma cylPred_telescopeNormalize (n : ℕ) (U : Set (X n)) (a : Σ m, I × X m) :
    cylPred n U (telescopeNormalize f a) = cylPred n U a := by
  obtain ⟨m, s, y⟩ := a
  unfold telescopeNormalize
  dsimp only
  split_ifs with hs
  · subst hs
    simp [cylPred]
  · rfl

/-- Open saturated subset `(0, 1) × U` inside the interior of the `n`-th cylinder. -/
private def cylSet (f : ∀ k, C(X k, X (k + 1))) (n : ℕ) (U : Set (X n)) :
    Set (MappingTelescope f) :=
  {z | Quotient.lift (s := Setoid.ker (telescopeNormalize f)) (cylPred n U)
    (fun a b hab => by
      rw [← cylPred_telescopeNormalize n U a, ← cylPred_telescopeNormalize n U b, hab]) z}

private lemma isOpen_cylSet {n : ℕ} {U : Set (X n)} (hU : IsOpen U) : IsOpen (cylSet f n U) := by
  refine isOpen_iff.2 fun m => ?_
  by_cases h : m = n
  · subst h
    convert (isOpen_Ioo (a := (0 : I)) (b := 1)).prod hU using 1
    ext ⟨s, y⟩
    exact ⟨fun ⟨_, hs, hy⟩ => ⟨hs, hy⟩, fun ⟨hs, hy⟩ => ⟨rfl, hs, hy⟩⟩
  · convert isOpen_empty using 1
    ext ⟨s, y⟩
    exact iff_false_intro fun ⟨hm, _⟩ => h hm

private def seamPred (f : ∀ k, C(X k, X (k + 1))) (n : ℕ) (U : Set (X n)) :
    (Σ m, I × X m) → Prop
  | ⟨m, s, y⟩ =>
    (∃ h : m = n, (s : ℝ) < 1 / 2 ∧ h ▸ y ∈ U) ∨
    (∃ h : m + 1 = n, (1 / 2 : ℝ) < s ∧ h ▸ f m y ∈ U)

private lemma seamPred_telescopeNormalize (n : ℕ) (U : Set (X n)) (a : Σ m, I × X m) :
    seamPred f n U (telescopeNormalize f a) = seamPred f n U a := by
  obtain ⟨m, s, y⟩ := a
  unfold telescopeNormalize
  dsimp only
  split_ifs with hs
  · subst hs
    simp only [seamPred, Set.Icc.coe_zero, Set.Icc.coe_one]
    norm_num
  · rfl

/-- Open collar neighbourhood around `{0} × U` at stage `n`. -/
private def seamSet (f : ∀ k, C(X k, X (k + 1))) (n : ℕ) (U : Set (X n)) :
    Set (MappingTelescope f) :=
  {z | Quotient.lift (s := Setoid.ker (telescopeNormalize f)) (seamPred f n U)
    (fun a b hab => by
      rw [← seamPred_telescopeNormalize n U a, ← seamPred_telescopeNormalize n U b, hab]) z}

private lemma isOpen_seamSet {n : ℕ} {U : Set (X n)} (hU : IsOpen U) : IsOpen (seamSet f n U) := by
  refine isOpen_iff.2 fun m => ?_
  by_cases h : m = n
  · subst h
    convert (isOpen_lt (continuous_subtypeVal.comp continuous_fst)
      (continuous_const (y := (1 / 2 : ℝ)))).inter (hU.preimage continuous_snd) using 1
    ext ⟨s, y⟩
    exact ⟨by rintro (⟨_, hs, hy⟩ | ⟨hm, -⟩); exacts [⟨hs, hy⟩, by omega],
      fun ⟨hs, hy⟩ => Or.inl ⟨rfl, hs, hy⟩⟩
  · by_cases h' : m + 1 = n
    · subst h'
      convert (isOpen_lt (continuous_const (y := (1 / 2 : ℝ)))
        (continuous_subtypeVal.comp continuous_fst)).inter
        (hU.preimage ((f m).continuous.comp continuous_snd)) using 1
      ext ⟨s, y⟩
      exact ⟨by rintro (⟨hm, -⟩ | ⟨_, hs, hy⟩); exacts [absurd hm h, ⟨hs, hy⟩],
        fun ⟨hs, hy⟩ => Or.inr ⟨rfl, hs, hy⟩⟩
    · convert isOpen_empty using 1
      ext ⟨s, y⟩
      exact iff_false_intro (by rintro (⟨hm, -⟩ | ⟨hm, -⟩); exacts [h hm, h' hm])

private lemma eq_of_height_eq {n₁ n₂ : ℕ} {t₁ t₂ : I} (ht₁ : t₁ ≠ 1) (ht₂ : t₂ ≠ 1)
    {x₁ : X n₁} {x₂ : X n₂}
    (h : height f (mkCyl f n₁ (t₁, x₁)) = height f (mkCyl f n₂ (t₂, x₂))) :
    n₁ = n₂ ∧ t₁ = t₂ := by
  rw [height_mkCyl, height_mkCyl] at h
  have ht₁1 : (t₁ : ℝ) < 1 := lt_of_le_of_ne t₁.property.2 (Subtype.coe_ne_coe.2 ht₁)
  have ht₂1 : (t₂ : ℝ) < 1 := lt_of_le_of_ne t₂.property.2 (Subtype.coe_ne_coe.2 ht₂)
  have hn₁₂ : ¬ n₁ < n₂ := fun hlt => by
    have : (n₁ : ℝ) + 1 ≤ n₂ := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [t₂.property.1]
  have hn₂₁ : ¬ n₂ < n₁ := fun hlt => by
    have : (n₂ : ℝ) + 1 ≤ n₁ := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [t₁.property.1]
  obtain rfl : n₁ = n₂ := le_antisymm (not_lt.1 hn₂₁) (not_lt.1 hn₁₂)
  exact ⟨rfl, Subtype.ext (by linarith)⟩

private lemma t2_sep_same {n : ℕ} [T2Space (X n)] {t : I} (ht : t ≠ 1) {x₁ x₂ : X n}
    (hne : mkCyl f n (t, x₁) ≠ mkCyl f n (t, x₂)) :
    ∃ U₁ U₂ : Set (MappingTelescope f), IsOpen U₁ ∧ IsOpen U₂ ∧
      mkCyl f n (t, x₁) ∈ U₁ ∧ mkCyl f n (t, x₂) ∈ U₂ ∧ Disjoint U₁ U₂ := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hx₁, hx₂, hdisj⟩ :=
    t2_separation (fun h : x₁ = x₂ => hne (congrArg _ (Prod.ext rfl h)))
  by_cases ht0 : t = 0
  · subst ht0
    refine ⟨seamSet f n U₁, seamSet f n U₂, isOpen_seamSet hU₁, isOpen_seamSet hU₂,
      Or.inl ⟨rfl, by simp, hx₁⟩, Or.inl ⟨rfl, by simp, hx₂⟩,
      Set.disjoint_left.2 fun z => ?_⟩
    induction z using ind with
    | cyl m q =>
      rintro (⟨h₁, -, hy₁⟩ | ⟨h₁, -, hy₁⟩) (⟨h₂, -, hy₂⟩ | ⟨h₂, -, hy₂⟩)
      · subst h₁
        exact Set.disjoint_left.1 hdisj hy₁ hy₂
      · omega
      · omega
      · subst h₁
        exact Set.disjoint_left.1 hdisj hy₁ hy₂
  · have hmem : t ∈ Set.Ioo (0 : I) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht⟩
    refine ⟨cylSet f n U₁, cylSet f n U₂, isOpen_cylSet hU₁, isOpen_cylSet hU₂,
      ⟨rfl, hmem, hx₁⟩, ⟨rfl, hmem, hx₂⟩, Set.disjoint_left.2 fun z => ?_⟩
    induction z using ind with
    | cyl m q =>
      rintro ⟨rfl, -, h₁⟩ ⟨_, -, h₂⟩
      exact Set.disjoint_left.1 hdisj h₁ h₂

/-- **If every stage `X n` is Hausdorff, then so is the mapping telescope.** -/
instance [∀ n, T2Space (X n)] : T2Space (MappingTelescope f) where
  t2 z₁ z₂ hne := by
    by_cases hh : height f z₁ = height f z₂
    · induction z₁ using ind_ne_one with
      | cyl n₁ t₁ x₁ ht₁ =>
        induction z₂ using ind_ne_one with
        | cyl n₂ t₂ x₂ ht₂ =>
          obtain ⟨rfl, rfl⟩ := eq_of_height_eq ht₁ ht₂ hh
          exact t2_sep_same ht₁ hne
    · obtain ⟨V₁, V₂, hV₁, hV₂, hz₁, hz₂, hdisj⟩ := t2_separation hh
      exact ⟨height f ⁻¹' V₁, height f ⁻¹' V₂,
        hV₁.preimage (height f).continuous, hV₂.preimage (height f).continuous,
        hz₁, hz₂, hdisj.preimage (height f)⟩

/-- **If every stage `X n` is compactly generated, then so is the mapping telescope.** Since
`CompactlyGeneratedSpace` abbreviates `UCompactlyGeneratedSpace.{u}`, this covers both
`CompactlyGeneratedSpace` and universe-explicit `UCompactlyGeneratedSpace`. -/
instance [∀ n, UCompactlyGeneratedSpace.{v} (X n)] :
    UCompactlyGeneratedSpace.{v} (MappingTelescope f) := by
  refine uCompactlyGeneratedSpace_of_continuous_maps fun {W} _ g hg => ?_
  rw [isQuotientMap_sigma_mkCyl.continuous_iff, continuous_sigma_iff]
  intro n
  have hslice (x : X n) : Continuous fun t : I => g (mkCyl f n (t, x)) := by
    let k₀ : C(ULift.{v} I, MappingTelescope f) := ⟨fun s => mkCyl f n (s.down, x), by fun_prop⟩
    exact (hg (CompHaus.of (ULift.{v} I)) k₀).comp continuous_uliftUp
  let G : X n → C(I, W) := fun x => ⟨fun t => g (mkCyl f n (t, x)), hslice x⟩
  have hG : Continuous G := by
    refine continuous_from_uCompactlyGeneratedSpace G fun S h => ?_
    let k' : C(S × ULift.{v} I, MappingTelescope f) :=
      ⟨fun p => mkCyl f n (p.2.down, h p.1), by fun_prop⟩
    have hc : Continuous fun p : S × I => g (mkCyl f n (p.2, h p.1)) :=
      (hg (CompHaus.of (S × ULift.{v} I)) k').comp
        (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd))
    exact (ContinuousMap.curry ⟨fun p : S × I => g (mkCyl f n (p.2, h p.1)), hc⟩).continuous
  exact continuous_eval.comp ((hG.comp continuous_snd).prodMk continuous_fst)

end SeparationAndCompactGeneration

section BondingAndHomotopies

/-- The composite bonding map `X m → X n` along `f` for `m ≤ n`. -/
@[expose]
def bondOfLE (f : ∀ n, C(X n, X (n + 1))) {m n : ℕ} (h : m ≤ n) : C(X m, X n) :=
  (CategoryTheory.Functor.OfSequence.map (X := fun k => TopCat.of (X k))
    (fun k => TopCat.ofHom (f k)) m n h).hom

@[simp]
theorem bondOfLE_refl (m : ℕ) : bondOfLE f (le_refl m) = ContinuousMap.id (X m) :=
  congrArg TopCat.Hom.hom (CategoryTheory.Functor.OfSequence.map_id _ m)

@[simp]
theorem bondOfLE_succ (m : ℕ) : bondOfLE f m.le_succ = f m :=
  congrArg TopCat.Hom.hom (CategoryTheory.Functor.OfSequence.map_le_succ _ m)

@[simp]
theorem bondOfLE_comp_bondOfLE {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (bondOfLE f hmn).comp (bondOfLE f hkm) = bondOfLE f (hkm.trans hmn) :=
  (congrArg TopCat.Hom.hom
    (CategoryTheory.Functor.OfSequence.map_comp _ k m n hkm hmn)).symm

theorem bondOfLE_step {m k : ℕ} (h : m ≤ k) :
    bondOfLE f (Nat.le_succ_of_le h) = (f k).comp (bondOfLE f h) := by
  rw [← bondOfLE_comp_bondOfLE h k.le_succ, bondOfLE_succ]

@[simp]
theorem bondOfLE_apply_bondOfLE {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (x : X k) :
    bondOfLE f hmn (bondOfLE f hkm x) = bondOfLE f (hkm.trans hmn) x :=
  ContinuousMap.congr_fun (bondOfLE_comp_bondOfLE hkm hmn) x

/-- The canonical homotopy from `incl f n` to `(incl f (n + 1)).comp (f n)` traced out by the `n`-th
cylinder of the mapping telescope. -/
def inclHomotopy (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    (incl f n).Homotopy ((incl f (n + 1)).comp (f n)) where
  toContinuousMap := mkCyl f n
  map_zero_left _ := rfl
  map_one_left x := mkCyl_one n x

@[simp]
lemma inclHomotopy_apply (n : ℕ) (t : I) (x : X n) :
    inclHomotopy f n (t, x) = mkCyl f n (t, x) := (rfl)

/-- The canonical homotopy from `incl f m` to `(incl f n).comp (bondOfLE f h)` for `m ≤ n`,
obtained by concatenating the cylinder homotopies from stage `m` up to stage `n`. -/
def inclHomotopyOfLE (f : ∀ n, C(X n, X (n + 1))) :
    ∀ {m n : ℕ} (h : m ≤ n), (incl f m).Homotopy ((incl f n).comp (bondOfLE f h))
  | m, 0, h =>
    match m, Nat.eq_zero_of_le_zero h with
    | 0, rfl => (ContinuousMap.Homotopy.refl (incl f 0)).cast rfl
        (by rw [bondOfLE_refl, ContinuousMap.comp_id])
  | m, k + 1, h =>
    if hmn : m = k + 1 then
      match m, hmn with
      | _, rfl => (ContinuousMap.Homotopy.refl (incl f (k + 1))).cast rfl
          (by rw [bondOfLE_refl, ContinuousMap.comp_id])
    else
      let hk' : m ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne h hmn)
      ((inclHomotopyOfLE f hk').trans
        ((inclHomotopy f k).compContinuousMap (bondOfLE f hk'))).cast rfl
        (by rw [bondOfLE_step hk', ContinuousMap.comp_assoc])

@[simp]
lemma inclHomotopyOfLE_refl (m : ℕ) :
    inclHomotopyOfLE f (le_refl m) =
      (ContinuousMap.Homotopy.refl (incl f m)).cast rfl
        (by rw [bondOfLE_refl, ContinuousMap.comp_id]) := by
  cases m <;> simp [inclHomotopyOfLE]

lemma inclHomotopyOfLE_step {m k : ℕ} (h : m ≤ k) :
    inclHomotopyOfLE f (Nat.le_succ_of_le h) =
      ((inclHomotopyOfLE f h).trans
        ((inclHomotopy f k).compContinuousMap (bondOfLE f h))).cast rfl
        (by rw [bondOfLE_step h, ContinuousMap.comp_assoc]) := by
  have hne : m ≠ k + 1 := by omega
  simp [inclHomotopyOfLE, hne]

/-- The `m`-th stage inclusion is homotopic to `bondOfLE f h` followed by the `n`-th stage
inclusion. -/
theorem incl_homotopic_comp_bondOfLE {m n : ℕ} (h : m ≤ n) :
    (incl f m).Homotopic ((incl f n).comp (bondOfLE f h)) :=
  ⟨inclHomotopyOfLE f h⟩

/-- Every point `incl f m x` is joined by a path in the mapping telescope to
`incl f n (bondOfLE f h x)`. -/
theorem joined_incl_bondOfLE {m n : ℕ} (h : m ≤ n) (x : X m) :
    Joined (incl f m x) (incl f n (bondOfLE f h x)) :=
  ⟨(inclHomotopyOfLE f h).evalAt x⟩

end BondingAndHomotopies

end MappingTelescope

end TauCeti
